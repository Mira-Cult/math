# Odd simple Bol loops with unbounded derived nilpotency class

**Continuation of 0323:C0010 [context outside this selected packet: `../claims/C0010.md`], with the scoped independent reviews below.** For every integer c≥2, the endpoint proved here is an explicit finite simple proper odd left Bol loop whose canonical left multiplication group G has nilpotent derived subgroup G′ of class exactly c, with Z(G′)≤Z(G). This rules out any universal nilpotency-class bound even in the central-center odd branch. It is a construction theorem, not exhaustion or an isomorphism classification of all higher-class envelopes. The [reviewed class-two parameterization](odd-central-class-two-classification.md), source `598fa119be327480c829af2a9beb709b02886bc4`, is the baseline; the remaining gap tested here is whether higher classes actually occur in simple folders.

Fix distinct odd primes p,q>c, let r=ord_q(p), s=ord_p(q), E=F_{p^r}, F=F_{q^s}, and choose λ∈E×, η∈F× of orders q,p respectively. The construction below has order

    p^{(c+1)r} q^{2rs+1}.                                (1)

There are two distinct primes larger than every fixed c, so this supplies every claimed class under the stated interfaces. No literature-novelty claim is made.

## Lie algebra, group and stabilizer data

Let L⁺ be the E-Lie algebra with basis x,y₁,…,y_c and nonzero basic brackets [x,y_j]=y_{j+1} for 1≤j<c. It is the semidirect product of Ex with an abelian space on which x shifts the chain, so Jacobi holds. Its class is c and center Ey_c. Take a second copy on x′,y₁′,…,y_c′ and form the central product identifying y_c=y_c′=z, with all mixed brackets zero. Denote the resulting algebra by L. It has E-dimension 2c+1, center Ez, and class c. Indeed a central vector has zero x,x′ coordinates by bracketing with y₁,y₁′, and then all y_j,y_j′ coefficients for j<c vanish by bracketing with x,x′. The bracket chain ending in z has length c.

Let τ_P exchange the copies and fix z. Let b generate A_q=C_q and act on the first copy by

    x↦λx,   y_j↦λ^{−(c−j)}y_j,

with inverse weights on the second copy. The bracket relations are preserved; z is fixed; τ_P inverts b. Every noncentral weight is nontrivial since q>c. Give x,y₁,x′,y₁′ degree one, y_j,y_j′ degree j and z degree c; this grading agrees with the lower central filtration from degree two onward.

Regard L as an F_p-Lie algebra. Since c<p, the BCH/Lazard correspondence gives an exponent-p group P with this underlying set, class c and center Ez. The precise source is [d’Elbée–Müller–Ramsey–Siniora, arXiv:2310.17595v3](../REFERENCES.md#lazard-bch-interface), §2.3, Facts 2.13 and 2.14, including subgroups, ideals and automorphisms. Restriction of scalars leaves the bracket chains and center unchanged. Both τ_P and A_q act as group automorphisms. Define

    𝔰_P=Ex ⊕ ⊕_{j=1}^{c−1}Ey_j′,    S_P=exp(𝔰_P).

This subalgebra is abelian; it is A_q-invariant, disjoint from its τ-image and the center, and complementary to its τ-image modulo the center. A_q acts without nonzero fixed vectors on 𝔰_P and on L/Ez, even for every nonidentity power of b.

Put A_p=(E,+), identified with Z_P=Z(P), and choose an F_p-basis to write a∈A_p as (a₁,…,a_r). Let W=⊕_{j=1}^rF², with the nondegenerate alternating F_q-form β equal to the sum of the field traces of the standard forms on the F² planes. Let R(a) multiply the j-th plane by η^{a_j}. These commuting operators are β-self-adjoint, faithful as a combined A_p-action, and have no common nonzero fixed vector. A nonzero a need not move every plane.

Take the exponent-q extraspecial group Q with coordinates W⊕W⊕F_q and product

    (u,v,t)(u′,v′,t′)
      =(u+u′,v+v′,t+t′+½[β(u,v′)+β(v,u′)]).

Let τ_Q swap u,v and fix t, while a acts by (R(a),R(a)⁻¹,1). A_q acts trivially on Q and A_p trivially on P. Set

    A=A_p×A_q,   G=(P×Q)⋊A,
    τ=(τ_P,τ_Q) with inversion on A,
    S_Q={(u,0,0):u∈W},
    H=(S_P×S_Q)⋊{a z(a):a∈A},

where z:A→Z_P×Z_Q identifies A_p with E and b with the unit generator of Z_Q=F_q. All central labels are fixed by G and τ. The twisted torus is a subgroup, since it is a central twist of the abelian complement A and has the same orders.

The A-action on P×Q is faithful. Its commutator subgroup is P×Q. For P, the fixed-free action on L/Z_P gives full commutator image on P/P′ by coprime averaging; Z_P≤P′=Φ(P), so the Frattini generation argument applies. For Q, the common fixed space of A_p on Q/Z_Q is zero, and the same argument applies with Φ(Q)=Z_Q. Thus

    G′=P×Q,   class(G′)=c,   Z(G)=Z_P×Z_Q=Z(G′).        (2)

These Frattini equalities use exponent-p and exponent-q in this construction; they are not imported into the arbitrary-exponent class-two theorem.

## Full marked transversal and canonical group

Put K={g∈G:τ(g)=g⁻¹}, and Λ=τ̂^G=τ̂K in G⋊⟨τ̂⟩. Oddness gives this single outside-involution class. The swaps and fixed centers give

    |C_P(τ)|=p^{(c+1)r},    |C_Q(τ)|=q^{2rs+1},
    |H|=|C_G(τ)|=p^{(c+1)r}q^{2rs+1},   |G|=|H|².

Hence |K|=[G:H]. We prove H∩Λ²=1 by showing that no nonidentity h∈H is inverted by an outside involution. Every element of Λ² is inverted by one of its two involution factors.

Write h=(s_P,s_Q)a z(a), with labels a_p∈A_p and a_q∈A_q. If a_p≠0, inspect the image in P⋊A_q. If also a_q≠1, the action of a_q on abelian S_P is fixed-point-free, so conjugation within S_P removes s_P. The remaining element is z_P(a_p)a_q, whose nontrivial p-primary component is z_P(a_p). An outside involution fixes this central component pointwise and therefore cannot invert the element. If a_q=1 and s_P≠1, the lowest nonzero graded component of log s_P lies in 𝔰_P. An outside involution sends it into the A_q-scaled opposite graded subspace τ𝔰_P, disjoint from it. Inner conjugation does not change the lowest lower-central component, so inversion is impossible. If s_P=1, the nonzero central label itself cannot be inverted.

If a_p=0 but a_q≠1, inspect Q⋊A_p, where the image is s_Q z_Q(a_q) with zero A_p-label. A nonzero S_Q shadow cannot be inverted: inner conjugacy is trivial on Q/Z_Q, the torus preserves the two halves and τ interchanges them. If its shadow is zero, its nonzero fixed central label prevents inversion. Finally if both labels vanish, a nonzero S_P or S_Q component is excluded by the same graded or half-space argument. This proof never assumes that every nonzero A_p-element is fixed-point-free on all Q-planes.

Thus H∩Λ²=1. As Λ²=K² is G-conjugacy invariant, the same holds for every conjugate of H; the size equality makes K a full transversal. It is inverse- and sandwich-closed, so the pinned C0001 correspondence gives a left Bol loop. A⊂K and ⟨K⟩ is normal in odd G because K is the set of τ-commutators. The commutator-generation argument above gives ⟨K⟩=G. A normal subgroup of G contained in H meets P×Q trivially: its Sylow intersections are normal in the respective p-groups and any nontrivial such subgroup meets the center, which H avoids. It then centralizes P×Q. The faithful action makes that centralizer Z_P×Z_Q, also disjoint from H. Hence the folder is faithful and G is the canonical left multiplication group. Formula (1) follows.

## Normal-subgroup defect and simplicity

Let N◁G be τ-stable, L_P=N∩P, L_Q=N∩Q, C_P=L_P∩Z_P and C_Q=L_Q∩Z_Q. Write T_p×T_q for the image of N in A, and J_p×J_q for that of H∩N. Subgroups decompose this way because p≠q. Fixed elements have trivial odd A-image, so C_N(τ)=C_{L_P}(τ)×C_{L_Q}(τ).

By the Lazard ideal correspondence, log L_P is an F_p-subspace and ideal. Coprime A_q averaging splits it into its central part C_P and a part V with no trivial A_q-weight; the averaging projection on L itself is exactly its projection onto Ez. It commutes with τ. Projection along V₋ injects 𝔰_P∩log L_P into V₊, because 𝔰_P and τ𝔰_P are disjoint modulo the center. Consequently

    |C_{L_P}(τ)|/|S_P∩L_P|≥p^{dim_Fp C_P}.              (3)

The analogous half-space argument in Q gives

    |C_{L_Q}(τ)|/|S_Q∩L_Q|≥q^{dim_Fq C_Q}.              (4)

Any nontrivial normal L_P or L_Q meets its respective center.

We next prove J_p≤C_P under A_p≅Z_P, and J_q≤C_Q under A_q≅Z_Q. Choose a p-element h∈H∩N with a prescribed J_p-label; its A_q-label is zero. In P its conjugation is that of exp(s), s∈𝔰_P, because A_p acts trivially on P and its central twist is fixed. Normality gives [exp(s),P]≤L_P. In P/L_P the image of exp(s) is therefore central. The Lazard correspondence identifies centers and ideals, so [s,L]≤log L_P. Equivalently, this follows by taking the logarithm of the nilpotent conjugation operator exp(ad_s); all required denominators are prime to p because c<p.

Project hτ(h)∈N∩(P×Q) to P. Its logarithm is BCH(s,τs) plus twice the prescribed central label. Every nonlinear BCH term lies in log L_P, since it is a Lie word in s,τs containing a bracket, [s,L]≤log L_P, and log L_P is an ideal. Averaging under A_q kills s+τs and preserves the central label. It follows that twice that label, and hence the label, belongs to C_P. This proves J_p≤C_P. The same argument in the class-two factor Q, using the pure q-label, trivial own-prime action and averaging under A_p, proves J_q≤C_Q. These are original-group normality arguments, not quotient-transversal assumptions.

The kernel of H∩N→J is (S_P∩L_P)×(S_Q∩L_Q). Thus (3)–(4) imply

    |C_N(τ)|/|H∩N|
      ≥p^{dim C_P−dim J_p}q^{dim C_Q−dim J_q},          (5)

with nonnegative exponents. If T_p=T_q=1 and N≠1, a nonzero local normal subgroup meets its center and gives strict defect. If T_q=1 and T_p≠1, some nonzero T_p element acts nontrivially on Q/Z_Q, by faithfulness. Its commutators force L_Q≠1, hence C_Q=Z_Q, whereas J_q=1. The defect is strict.

If T_q≠1, then T_q=A_q. A lift acts fixed-point-freely on P/Z_P, so its commutators have full image on P/P′; the Frattini argument forces L_P=P. If T_p is proper in A_p, then dim C_P=r>dim J_p and the defect is again strict. Finally, if T_q=A_q and T_p=A_p, commutators with all of A_p give full Q/Z_Q, so Q≤N as well and N=G. All proper nontrivial τ-stable N therefore have strict defect. The reviewed criterion at `65a3e58df517df59656ab948ac9d122208f62c4a` proves simplicity. This invocation retains its maximal-simple-quotient argument and the cited canonical inversion interfaces.

## A direct Moufang witness

The subgroup G₀=(Z_P×Q)⋊A suffices for a local multiplication calculation. Its intersection with H is H₀=S_Q⋊{a z(a)}. The K representatives of all G₀/H₀ cosets lie in G₀, by the same explicit Heisenberg section used in the reviewed operator construction: for coordinates (u,t_p,t_q) the P component is zero, the Q vectors are (−R(−t_p)u,u), the Q center is zero and the torus label is (−t_p,−t_q). Right-H₀ reduction gives exactly those coordinates. Uniqueness of the ambient K representative shows that multiplication on these cosets is the ambient loop multiplication and stays within this set. Neither faithfulness nor generation by K∩G₀ is assumed for this restricted action.

Its multiplication is

    (u,t_p,t_q)·(v,s_p,s_q)
      =(u+R(t_p)v, t_p+s_p, t_q+s_q−β(u,v)).            (6)

Choose a∈A_p with R(a)≠1, v with (R(a)−1)v≠0, and w with β((R(a)−1)v,w)≠0. Let X=(0,a,0), Y=(v,0,0), Z=(w,0,0). The two sides (XY)(ZX) and (X(YZ))X have equal vector and A_p coordinates, but their F_q central entries are −β(R(a)v,w) and −β(v,w). They differ, proving properness directly. There is no use of CFSG or the simple Moufang classification.

## Scope and verification boundary

The new proof depends on the precise Lazard source and the already reviewed full-inverted-set, faithful-folder and strict-defect interfaces. Root directly inspected arXiv:2310.17595v3, §2.3, Facts 2.13–2.14; a separate preliminary source/properness audit by [model reviewer identity omitted] also checked them. These inspections do not certify this full construction. The exact-source independent mathematical acceptances are recorded below. No computational certificate, formal verification or literature novelty is claimed.

This proves the central-center nilpotent-derived branch has no universal nilpotency-class bound under the stated inputs. It leaves the classification of the higher-class data, possible noncentral centers, nonnilpotent derived groups and all remaining even branches open. The parameters above are construction inputs, not a proved complete isomorphism invariant or an exhaustion theorem.

At exact source `722ba8c289c96dfd87c98f9a5ab3dcb8b2080998`, GPT-6.1 Terra reviewers [model reviewer identity omitted], [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the full construction theorem. All three checked the paired filiform Lie algebra, weights and field-degree handling, graded marked-inversion obstruction, transversal sizes, core-freeness, generation, arbitrary τ-stable normal-subgroup defects, central-label inclusions via ideals and averaging, all torus-image cases, and the explicit ambient-loop Moufang witness. Their acceptances retain the cited Lazard and previously reviewed folder/strict-defect interfaces. Reviewer [model reviewer identity omitted] also directly inspected the exact Lazard source and separately checked the restricted properness calculation; the other two relied on the recorded source inspection. No reviewer used a computation or asserted formal verification, novelty, an isomorphism classification of this family, or global exhaustion.
