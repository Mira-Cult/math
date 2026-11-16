# A simple odd Bol loop with a fixed noncentral derived shadow

**Continuation of 0323:C0010 [context outside this selected packet: `../claims/C0010.md`], with the scoped independent reviews below.** The endpoint is an actual simple proper odd left Bol loop with nilpotent derived envelope D, exponent-p Sylow factors of class less than p, Z(D)≤Z(G), but a nonzero common coprime fixed space on one P/Z(P). This refutes universality of condition 3 in the [central Lazard parameterization](odd-lazard-central-classification.md), independently accepted at `9819182787d94bd1502a03130e2500dbba936937`. That restricted theorem remains valid. The construction below has order 11⁶·5¹¹; it is not an exhaustion theorem or a novelty claim. The separately reviewed variant at the end refutes necessity of disjoint symmetric stabilizers.

## Lie data and canonical envelope

Over F₁₁ take the Lie algebra T with basis x,y,u,v,w,z and nonzero basic brackets

    [x,y]=u,   [x,u]=v,   [y,u]=w,
    [x,w]=[y,v]=z.                                     (1)

All other basic brackets vanish, with antisymmetry understood. Jacobi on x,y,u gives z−z=0. Any other triple of distinct basis vectors has zero Jacobi sum: an inner bracket involving v or w is central, and the remaining possible outer brackets vanish. Repeated arguments give zero by alternation. Its lower central series after T is ⟨u,v,w,z⟩, ⟨v,w,z⟩, ⟨z⟩, 0. Bracketing a central vector with x and y forces all coefficients except that of z to vanish. Thus T has class four and center F₁₁z.

Take a second copy, identify z=z′ and make all mixed brackets zero. The central product 𝔭 has dimension 11, class four and center Z_P=F₁₁z. Let σ exchange the copies and fix z. Let A₅=C₅ act with weights

    x:1, y:−1, u:0, v:1, w:−1, z:0

on the first copy and inverse weights on the second, using λ=3∈F₁₁ of order five. Each bracket in (1) respects its weights. The involution σ inverts A₅ and fixes the center. The A₅-fixed subspace of 𝔭/Z_P is exactly ⟨u,u′⟩, whereas its fixed subspace on 𝔭/[𝔭,𝔭] is zero.

The subspace 𝔰=⟨x,u,v,y′,w′⟩ is an A₅-invariant Lie subalgebra; its only nonzero basic bracket is [x,u]=v. We have

    𝔭=𝔰⊕σ𝔰⊕Z_P.                                     (2)

By the [Lazard correspondence](../REFERENCES.md#lazard-bch-interface), arXiv:2310.17595v3, §2.3, Facts 2.13–2.14, class four is less than eleven, so P=exp 𝔭 is an exponent-11 group, S_P=exp 𝔰 is a subgroup, and the stated center, class and automorphisms carry over. Let A₁₁=C₁₁ act trivially on P.

Let F=F_{5⁵}, since ord₁₁(5)=5, and choose η∈F× of order eleven. On W=F², viewed over F₅, let β be the field trace of the standard alternating form. This is nondegenerate. The scalar action R(a)=ηᵃ of A₁₁ is faithful, fixed-point-free for every a≠0 and β-self-adjoint. Form Q on W⊕W⊕F₅ with product

    (r,s,t)(r′,s′,t′)
      =(r+r′,s+s′,t+t′+½[β(r,s′)+β(s,r′)]).

It is extraspecial of exponent five, with center Z_Q=F₅. Let τ_Q swap r,s and fix the center; let A₁₁ act as (R(a),R(a)⁻¹,1), and A₅ act trivially. Put S_Q=W⊕0⊕0.

Set A=A₁₁×A₅, D=P×Q and G=D⋊A. Let τ restrict to σ,τ_Q and invert A. Identify A₁₁ with Z_P and A₅ with Z_Q through z:A→Z(D), and set

    H=(S_P×S_Q)⋊{a z(a):a∈A},
    K={g∈G:τ(g)=g⁻¹}.                                 (3)

The central graph is a subgroup normalizing both stabilizer factors. Equation (2) and the two Q-halves give H∩τ(H)=1: equality modulo the centers kills the two stabilizer shadows, and equality of the central labels then kills twice each torus label. The orders are

    |G|=11¹²·5²²,   |H|=|C_G(τ)|=11⁶·5¹¹.

The [symmetric envelope-factorization lemma](exact-factorization-criterion.md#symmetric-exact-factorizations-and-full-inverted-folders), reviewed at `7fbfbc5a56f4bb1ead9a4d6202c2d948a67950d8`, supplies the full Bol transversal and G-loop property.

The A₅ action has no fixed vector on P/Φ(P)=𝔭/[𝔭,𝔭], and A₁₁ has none on Q/Φ(Q). Commutators therefore generate each Frattini quotient and hence each Sylow factor. It follows that G′=D. Moreover A⊂K and ⟨K⟩ is normal in odd G, as the subgroup of τ-commutators. Thus ⟨K⟩=G.

For clarity, core-freeness uses more than abstract faithfulness of an action. If a∈A acts inner on both P and Q, its A₅-action on P has coprime order to the 11-group Inn(P), so that action is trivial and its A₅ label is zero. Its A₁₁-action on Q similarly forces its A₁₁ label to be zero. Hence C_G(D)=Z(D), and Z(G)=Z(D). A normal subgroup inside H intersects D trivially: a nontrivial Sylow intersection would be normal in that p-group and would meet its one-dimensional center, disjoint from H. Such a subgroup then centralizes D and lies in Z(D), again disjoint from H. Thus core_G(H)=1 and G is the canonical left multiplication group of the constructed loop.

## Simplicity for every τ-stable normal subgroup

Let N◁G be τ-stable, L_P=N∩P, L_Q=N∩Q, and T₁₁×T₅ its image in A. Let J₁₁×J₅ be the image of H∩N. These decompositions hold because the two primes are distinct. Since τ inverts A, its fixed elements have zero torus image. Consequently

    |C_N(τ)|/|H∩N|
      = (|C_{L_P}(τ)|/|S_P∩L_P|)
        (|C_{L_Q}(τ)|/|S_Q∩L_Q|) / (|J₁₁||J₅|).      (4)

Every nontrivial L_P contains the entire cyclic center Z_P, since it is normal in P. Put I=log L_P. Projection s↦(s+σs)/2 modulo Z_P injects 𝔰∩I into (I/Z_P)₊ by (2). Because σ fixes Z_P, its fixed count is 11·|(I/Z_P)₊|. Therefore the first local ratio in (4) is at least 11 whenever L_P≠1, and is one otherwise. The identical half-space argument gives a factor at least five whenever L_Q≠1. No averaging under A₅ and no fixed-point-free hypothesis on P/Z_P occurs here.

If J₁₁≠1, then L_P≠1. To see this, assume L_P=1 and lift a nonidentity J₁₁-label to an 11-element h∈H∩N. Its A₅ label is zero, and its A₁₁ part acts trivially on P. Since [h,P]≤N∩P=1, its S_P component must be central and hence trivial. Now hτ(h)∈N∩D has P-coordinate z_P(a)²≠1. The nilpotent subgroup N∩D splits into its Sylow factors, contradicting L_P=1. The analogous argument shows J₅≠1 implies L_Q≠1, since A₅ acts trivially on Q. Thus each denominator in (4), of order at most its prime, can cancel only a present local factor.

There are four torus-image cases. If T₁₁=T₅=1 and N≠1, a nontrivial local intersection gives strict inequality in (4), while both J factors are trivial. If T₁₁≠1 and T₅=1, a lift acts on Q/Φ(Q) by a nonidentity scalar of order eleven. Its inner component acts trivially on that quotient, so normality forces L_Q to project onto the whole Frattini quotient and hence L_Q=Q. As J₅=1, an uncancelled factor five remains. If T₅≠1 and T₁₁=1, the same argument on P/Φ(P), using its nontrivial A₅ weights, forces L_P=P and leaves an uncancelled factor eleven. If both torus images are nontrivial, these arguments force L_P=P,L_Q=Q and N=G.

Every nontrivial proper τ-stable normal subgroup therefore has strict defect. The reviewed [strict-defect criterion](odd-folder-radicals.md), source `65a3e58df517df59656ab948ac9d122208f62c4a`, gives simplicity, under its canonical odd-folder hypotheses verified above. This uses its maximal-simple-quotient proof; it does not assume that an arbitrary projected section is a quotient loop.

## Properness and the obstruction

Use G₀=(Z_P×Q)⋊A and H₀=G₀∩H. Exactly the restricted section calculation in the [unbounded-class construction](odd-unbounded-derived-class.md#a-direct-moufang-witness), reviewed at `722ba8c289c96dfd87c98f9a5ab3dcb8b2080998`, applies: for coordinates (u,t₁₁,t₅), its inverted representative has zero P-component, Q-vectors (−R(−t₁₁)u,u), zero Q-center and torus label (−t₁₁,−t₅). These representatives lie in G₀; uniqueness of the ambient K-section makes the resulting subset an actual subloop. Its multiplication is

    (u,t₁₁,t₅)·(v,s₁₁,s₅)
      =(u+R(t₁₁)v,t₁₁+s₁₁,t₅+s₅−β(u,v)).            (5)

Choose a≠0 and v,w with β((R(a)−1)v,w)≠0. For X=(0,a,0), Y=(v,0,0), Z=(w,0,0), the Moufang expressions (XY)(ZX) and (X(YZ))X have central coordinates −β(R(a)v,w) and −β(v,w), respectively. They differ. Thus the loop is proper, without CFSG or a simple Moufang classification.

Its derived 11-Sylow has class four and exponent eleven, its derived 5-Sylow has class two and exponent five, and their centers are central in G. Yet C_{P/Z_P}(A₅)=exp⟨u,u′⟩ modulo Z_P is nontrivial. These are canonical envelope invariants, so this is a counterexample to universal derivability of condition 3. The higher-class classification must allow noncentral fixed shadows and potentially nonabelian stabilizer subalgebras such as 𝔰 here. It does not follow that every such envelope has the split central-graph form (3).

At exact source `396d468577c78a43d2c4d1f4821b074ddfd477ea`, GPT-6.1 Terra reviewers [model reviewer identity omitted], [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the full construction above, retaining the cited Lazard, symmetric-factorization and strict-defect interfaces. Each checked the Lie algebra, weights and original stabilizer, the canonical faithful generated folder, all τ-stable normal-subgroup cases including nonsplit lifts, and the actual restricted-section Moufang witness. No full loop table, computational certificate, fresh primary-source audit, formal verification or literature-novelty audit was performed. Those reviews do not cover the following variant, whose separate acceptance is recorded below.

## An overlapping-stabilizer variant

**Further result with the scoped independent reviews below.** Keep G,τ,P,Q,A and all central labels above, and replace only 𝔰 by

    f=u+u′,   𝔰*=⟨x,f,v,y′,w′⟩,   S*=exp 𝔰*.

The only nonzero basic brackets in this subalgebra are [x,f]=v and [y′,f]=w′. With M=⟨x,v,y′,w′⟩, it is the semidirect sum F₁₁f⋉M, with M abelian. The A₅ generator fixes f and acts by the scalar λ on all of M. Set H*=(S*×S_Q)⋊{a z(a)}. Its order, center avoidance and core-freeness are unchanged, but

    H*∩τ(H*)=exp⟨f⟩≠1.                               (6)

Indeed equality of torus labels and comparison of central coordinates first force the graph labels to vanish; the remaining P-intersection is the displayed line and the Q-halves are disjoint. This comparison uses that 𝔰* and σ𝔰* have zero central coordinate: a central equality of their group elements is an additive equality of their logarithms. Therefore the symmetric exact-factorization lemma cannot establish this variant's transversal.

We prove the full marked collision condition directly. Let Λ be the full outside-involution class in G⋊⟨τ̂⟩; oddness gives Λ=τ̂K, and |K|=[G:H*] from the unchanged fixed-centralizer count. Every element of Λ² is inverted by one of its factors. It is enough to show that no nonidentity h∈H* is inverted by any member of Λ.

First observe the lower-central graded obstruction on S*. On degree one, its shadow lies in ⟨x,y′⟩, whose image under σ and any A₅ weights lies in the disjoint ⟨x′,y⟩. When that vanishes, its degree-two shadow is a multiple of f, fixed by σ and A₅. When that also vanishes, its degree-three shadow lies in ⟨v,w′⟩, exchanged with the disjoint ⟨v′,w⟩. There is no remaining degree-four coordinate in 𝔰*. Inner P-conjugation is trivial on each lower-central factor, and the other Sylow and A₁₁ centralize P. Thus the first nonzero shadow of an S* element cannot be negated by any marked involution.

Write h=(s_P,s_Q)a z(a). If its A₁₁ label is nonzero, inspect the homomorphic image in P⋊A₅. If its A₅ label is zero, the preceding graded argument excludes inversion of s_P z_P when s_P≠1; if s_P=1, its nonzero fixed central label excludes inversion. If instead its A₅ label is bʲ with j≠0, write s_P=exp(m)exp(tf), m∈M. Conjugation on the abelian exp M by exp(tf)bʲ has linear operator λʲ exp(t ad_f), so one minus this operator is invertible: its eigenvalues are all 1−λʲ≠0. Conjugating by an element of exp M≤H* therefore removes m. The remaining P⋊A₅ image is exp(tf)z_P bʲ, with commuting 11- and 5-parts. Inversion would invert its 11-primary part exp(tf)z_P. For t≠0 that part has the τ-fixed nonzero degree-two shadow tf, impossible; for t=0 its nonzero central label is fixed, also impossible. This conjugation preserves H* and the marked collision question.

If the A₁₁ label is zero and the A₅ label is nonzero, inspect Q instead. The image is s_Q z_Q, with no A₁₁ action and with z_Q≠1. A nonzero S_Q shadow is sent into the other Q-half by any marked involution and cannot be negated; if the shadow is zero, the fixed central label excludes inversion. Finally, if both torus labels vanish, use the first nontrivial S* or S_Q component and its graded or half-space obstruction. These cases prove H*∩Λ²=1. Conjugacy invariance of Λ² and the count above give every conjugate transversal. Full inversion gives inverse- and sandwich-closure, so this is a left Bol folder. The previous generation and core arguments still apply and make G canonical.

The simplicity proof above also extends, with one change justified here. The shadow of 𝔰* intersects the negative σ-eigenspace of 𝔭/Z_P trivially: its four moving coordinates occupy disjoint swapped pairs, while f is positive. Hence for every nonzero σ-stable ideal I containing Z_P, the plus projection injects 𝔰*∩I into (I/Z_P)₊. This gives the same local factor eleven in (4). Center avoidance, trivial own-prime action and the Frattini actions are unchanged, so both J_i≠1⇒L_i≠1 arguments and all four torus-image cases apply verbatim with S*. Every proper nonzero invariant normal again has strict defect. The same G₀,H₀ and actual subloop (5) give the same direct Moufang failure. Thus the variant is a simple proper loop of the same order, with nontrivial stabilizer overlap (6).

It is nevertheless a G-loop. Put r=u−u′ and U=exp⟨r⟩. We have σr=−r, A₅ fixes r, [r,x]=−v, [r,y′]=w′ and the other brackets with 𝔰* vanish. Thus U normalizes H*, U∩H*=1, and N₀=H*U is a subgroup of N_G(H*) of order 11|H*|. A τ-fixed element of N₀ has zero torus label and zero Q-component. Its P-component lies in exp(𝔰*+⟨r⟩). In degree one τ-fixedness kills x,y′; in degree three it kills v,w′; in degree two it kills r and leaves f. No central coordinate is present in this subalgebra. Therefore C_{N₀}(τ)=exp⟨f⟩ and

    |τ̂^{N₀}|=|N₀|/11=|H*|=|Λ|.

The normalizer is transitive on the marked class. For every k∈K its conjugation can send τ̂ to τ̂k while preserving H*, and therefore sends K to k⁻¹K. The general principal-isotope interface reviewed at `ea836a5f328d6bc52913aac8fd1841a87072f5f8` gives the G-loop conclusion. Nontrivial overlap alone does not obstruct that property.

The two constructions here are nonisomorphic: any loop isomorphism preserves its canonical G,H and inversion automorphism τ, hence the order of H∩τ(H), which is one for the first construction and eleven for the variant. The variant refutes necessity of symmetric stabilizer factorization even under central-center, nilpotent-derived Lazard hypotheses, while leaving general G-loop necessity open. At exact source `f214f853346713f234786fdbf5566608a6aec26b`, GPT-6.1 Terra reviewers [model reviewer identity omitted], [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted this entire extension. Each checked the stabilizer intersection, full graded and mixed-torus marked collision proof, all-conjugate transversals, applicability of the all-normal strict-defect and Moufang arguments, normalizer and fixed-point counts, G-loop conclusion and canonical nonisomorphism invariant. Their acceptances retain the preceding construction and its cited Lazard, folder, strict-defect and principal-isotope inputs. No computation, formal verification, novelty or universal G-loop claim is made.

The [fixed-envelope stabilizer continuation](odd-fixed-envelope-stabilizers.md) addresses all A₅-stable stabilizer subalgebras in this same graph and envelope, including a third concrete simple loop whose G-loop proof uses an outer automorphism. It has three independent acceptances at `d64289bb37659dc6fc95963f1e9b3323c3b22dfa`, with its own precise scope; it does not enlarge the scope of the earlier acceptances above.
