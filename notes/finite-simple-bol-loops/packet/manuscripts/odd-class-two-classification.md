# All odd simple Bol folders with class-two derived group

**Continuation of 0323:C0010 [context outside this selected packet: `../claims/C0010.md`], with three independent exact-source acceptances recorded below.** The precise endpoint is construction, exhaustion, an exact finite simplicity test and a complete equivalence relation for every finite simple nonassociative odd left Bol loop whose canonical left multiplication group G has derived subgroup D=G′ of nilpotency class at most two. There is no exponent or center-centrality restriction. The resulting description is in finite abelian groups, bimaps, actions and cocycles, with explicit quadratic and subgroup tests. It is not a closed list of bimap orbits, an efficiency bound, or a classification outside this derived-group branch.

The baseline [central class-two parameterization](odd-central-class-two-classification.md), reviewed at `598fa119be327480c829af2a9beb709b02886bc4`, did not cover the [noncentral Jordan-center family](odd-noncentral-jordan-center-family.md), reviewed at `379317e583fa1e0c9171d526562c4f7e484d7d19`. The new [coprime-center reduction](odd-class-two-coprime-center-reduction.md), reviewed at `30d3ddf2d4a99650d08b4add502402a383f91447`, supplies the missing universal restriction: for every Sylow P_i of D, B_i=(G/D)_{p_i′} fixes Z(P_i) and has no fixed point on P_i/Z(P_i). Own-prime center actions remain unrestricted here, subject to the exact tests below.

The source interfaces are the canonical folder and inversion statements C0001/C0007; G=HD and the odd-envelope facts at `e896039d004ff3882621aca115b1a39cc8fed207`, `95f226ac6c02b0153f3c226d823518e0891c1f1d` and FKP application `ab4059e6a9b8d5876e2bffa993bb98e7dac69025`; the faithful stabilizer-action lemma at `379317e583fa1e0c9171d526562c4f7e484d7d19`; and the strict-defect iff simplicity criterion at `65a3e58df517df59656ab948ac9d122208f62c4a`. Their qualifications remain in [odd-folder-radicals.md](odd-folder-radicals.md). The arbitrary-exponent class-two Lie-ring interface uses addition xy[x,y]^{−1/2}, not an exponent-p vector-space assumption. Unique halving is used throughout.

## Construction data

Choose a finite nonempty set of distinct odd primes p_i. For each i choose nonzero finite abelian p_i-groups W_i,Z_i, an involution σ_i on Z_i, and a biadditive map b_i:W_i×W_i→Z_i satisfying

    σ_i b_i(x,y)=−b_i(y,x).

On U_i=W_i⊕W_i define

    Ω_i((x,y),(x′,y′))=b_i(x,y′)−b_i(x′,y).         (1)

Require Ω_i to have zero radical and its values to generate Z_i. Let A_i be a finite abelian p_i-group of order |Z_i^{σ_i}|, put A=∏A_i and B_i=∏_{j≠i}A_j. Choose actions R_i:A→Aut(W_i), T_i:A→Aut(Z_i) with

    σ_i T_i(a) σ_i=T_i(a)⁻¹,
    b_i(R_i(a)x,R_i(a)⁻¹y)=T_i(a)b_i(x,y).            (2)

Require T_i(B_i)=1, C_{W_i}(B_i)=0, and the combined R_i-action to be faithful. These are finite abelian-group conditions; no homocyclicity or simultaneous scalar action is assumed. A trivial A_i is syntactically allowed by its order condition, but the eventual simplicity test excludes impossible simple cases.

Put Z=∏Z_i. Supply a normalized crossed cocycle f:A→Z, with components f_i, such that

    f(ab)=f(a)+T(a)f(b),
    T_i(a)σ_i f_i(a)=f_i(a) for every i,a.             (3)

The second equation is the positive-eigenspace condition for the involution T_i(a)σ_i; it does not say that f_i(a) is σ_i-fixed. As B_i acts trivially on Z_i and has coprime order, f_i|B_i=0 automatically.

Let P_i be the class-two BCH group on U_i⊕Z_i, with central product correction ½Ω_i. Set D=∏P_i and G=D⋊A. The action on U_i is ρ_i(a)=R_i(a)⊕R_i(a)⁻¹, and its action on Z_i is T_i(a). Let τ swap the two W_i coordinates, act by σ_i on Z_i and invert A. Equations (1)–(2) make it an automorphism. Set

    S_i=W_i⊕0⊕0,   S=∏S_i,
    H=S⋊{f(a)a:a∈A},   K={g∈G:τ(g)=g⁻¹}.           (4)

The cocycle makes its graph a subgroup and it normalizes S. Two finite tests select the valid simple folders; the proof below shows that every loop in the endpoint has such data.

## Exact quadratic test for the full transversal

For a∈A define the subgroup

    Z_{i,−}(a)=ker(σ_i+T_i(a)⁻¹)≤Z_i.

The elements of K above a have i-th coordinates

    (x_i,−R_i(a)⁻¹x_i,z_i),   z_i∈Z_{i,−}(a).        (5)

For every a,c∈A with ac≠1 require at least one i for which

    f_i(ac) ∉ Z_{i,−}(a)+T_i(a)Z_{i,−}(c)
      + {½ b_i((1−R_i(ac))x,R_i(a)⁻¹x):x∈W_i}.     (6)

The braces denote an image set, not a subgroup or linear span. Thus (6) is an explicit finite quadratic membership test over the chosen finite abelian groups.

To derive it, multiply (5) above a and c. For their product to lie in H, its second W-coordinate must vanish, forcing the second chosen vector to be −R_i(c)x_i. The first coordinate becomes (1−R_i(ac))x_i, and the center is

    z_i+T_i(a)w_i
      +½ b_i((1−R_i(ac))x_i,R_i(a)⁻¹x_i).

Membership in H is exactly equality of this center with f_i(ac) at every i. If ac=1, both vector coordinates vanish and any such H-element is the identity. This proves that (6) is equivalent to H∩K²=1.

The involution T_i(a)σ_i is conjugate to σ_i by T_i(a^{1/2}), since A has odd order. Hence |Z_{i,−}(a)|=|Z_i^-|, and

    |K|=|A|∏|W_i||Z_i^-|=∏|W_i||Z_i|=[G:H].

The full outside-involution class in odd G gives G-invariance of K². Therefore (6) supplies all conjugate transversals; full inversion supplies inverse- and sandwich-closure. These conditions are necessary and sufficient for the constructed section to be a left Bol folder.

The data also make G its canonical group. Coprime fixed-point-freeness gives [U_i,B_i]=U_i, so commutators with A project onto each U_i. If their normal closure in P_i is M_i, then P_i=M_iZ_i and Z_i=P_i′, whence P_i′=M_i′≤M_i and M_i=P_i. This proves G′=D and, since pure A⊂K and ⟨K⟩ is normal in odd G, ⟨K⟩=G. It does not use Φ(P_i)=P_i′, which need not hold at arbitrary exponent.

If an A-element acts inner on D, it acts trivially on every U_i. Faithfulness of the R_i then makes it the identity, so C_G(D)=Z(D). A normal subgroup inside H cannot meet D nontrivially without meeting a Sylow center, whereas H∩Z(D)=1. It therefore centralizes D, lies in Z(D)⊂D and is trivial. The folder is faithful.

## Exact subgroup test for simplicity

For each i choose A- and τ-invariant subgroups V_i≤U_i and C_i≤Z_i such that

    Ω_i(V_i,U_i)⊆C_i.                                (7)

Choose a subgroup T≤A satisfying, for every t∈T,

    (ρ_i(t)−1)U_i⊆V_i,   (T_i(t)−1)Z_i⊆C_i.         (8)

In Z_i/C_i the A-fixed subgroup is σ_i-stable. Choose an ordinary group homomorphism

    u:T→∏((Z_i/C_i)^A)_−,                            (9)

where the minus sign denotes σ_i-negative elements. These tuples describe every τ-stable normal subgroup, with no assumption that its torus lifts split. Specifically, the subgroup consists of all elements with torus t∈T, vector components in V_i, and central components congruent to u_i(t) modulo C_i.

For completeness, let N be such a normal subgroup. Its intersection with P_i is an ideal of the class-two Lie ring. Coprime B_i averaging, with B_i trivial on Z_i and fixed-point-free on U_i, removes every possible central graph offset of that ideal, leaving exactly V_i⊕C_i. Condition (7) is its bracket normality. For a lift of t in N, normality under B_i and fixed-point-freeness on U_i/V_i put its vector in V_i, so it can be removed. The remaining central class is u_i(t). Normality under A makes it A-fixed, and normality under D gives (8). In particular T acts trivially on Z_i/C_i, so the crossed-cocycle law for u reduces to an ordinary homomorphism. τ-stability then says σ_i u_i(t)=−u_i(t), proving (9).

Conversely (7)–(9) define a subgroup normal under A and D and stable under τ. In the D-conjugation check, the extra BCH central term is ½Ω_i(v,(ρ_i(t)−1)v), which lies in C_i by (7)–(8). Every odd-order subgroup C_i is closed under unique halving. This verifies the central correction as well as the vector condition. Thus the tuples are exhaustive.

For a tuple put

    J={t∈T:f_i(t)+C_i=u_i(t) for every i}.

Then

    |C_N(τ)|/|H∩N|
      = (∏|C_i^{σ_i}| |V_i^τ|)
        / (|J| ∏|V_i∩(W_i⊕0)|).                     (10)

Indeed fixed elements have zero torus label; the fixed count is that of the direct ideals. The stabilizer intersection has vector kernel displayed in the denominator and torus image J. The central splitting used above ensures that no first-half vector cancels a central class outside C_i. On T, f modulo C is a homomorphism by (8), so J is a subgroup.

Require the ratio in (10) to be strictly greater than one for every tuple representing a nonidentity proper N. The identity tuple has all V_i,C_i zero and T=1; the full tuple has V_i=U_i,C_i=Z_i,T=A and its forced zero u. The reviewed strict-defect criterion makes this exactly simplicity. The test is over finite subgroup/action data rather than loop multiplication tables, but no complexity bound or short list of its solutions is claimed.

## Exhaustion and preservation of the original loop

Now start from a loop in the stated endpoint. For each Sylow P_i, the reviewed coprime-center reduction gives B_i-centrality of Z_i=Z(P_i) and C_{U_i}(B_i)=0. The faithful-stabilizer-action lemma gives H∩Z(D)=1. In particular S_i=H∩P_i is abelian and its shadow W_i is isotropic and A-invariant.

The Hall-normalizer splitting argument used in the [central Lazard normal form](odd-lazard-central-classification.md), reviewed at `9819182787d94bd1502a03130e2500dbba936937`, applies to these finite abelian kernels U_i without an exponent assumption. In an extension of Γ=A⋊⟨τ̂⟩ by U_i, the inverse image of its normal coprime B_i has conjugate complements. For a complement chosen τ-compatible, the normalizer maps onto Γ and has kernel C_{U_i}(B_i)=0; it is therefore a Γ-complement. Taking the fiber product of the local quotients gives a global Γ-complement in (G/Z(D))⋊⟨τ̂⟩ containing the actual τ̂. Let A₀ be its inverted A-part.

Align the local B_i-complements in H by U_i-conjugation. Their normalizers inside H then force the pure A₀ in each local quotient. The conjugators lift to the commuting P_i, so a single d∈D gives an actual conjugate H₀ with

    G/Z(D)=(∏U_i)⋊A₀,
    H₀Z(D)/Z(D)=(∏W_i)⋊A₀.                           (11)

All these stabilizers retain the original full-conjugate transversal property. No quotient by a nonnormal W_i is used. If E₀ is the preimage of A₀, C=E₀∩H₀ maps onto A: remove the W_i coordinates using the actual S_i before lifting (11). Its kernel lies in H₀∩Z(D)=1. Thus C≅A is abelian, G=D⋊C and E₀=Z(D)⋊C. E₀ need not be a direct product.

Write τ(c)=δ(c)c⁻¹ for c∈C, with δ(c)∈Z(D), and let T(c) denote its center action. Then σδ(c)=T(c)δ(c). The map χ(c)=T(c)δ(c) is a T-cocycle: the inverse-action cocycle identity for δ and commutativity of C give χ(cd)=χ(c)+T(c)χ(d). Set e(c)=−χ(c)/2. The subgroup {e(c)c:c∈C} is a complement inverted by τ, since σe(c)+δ(c)=−T(c)⁻¹e(c). Use it as the pure A in (4). The old C is its graph f=χ/2, satisfying both equations (3). Shifting by these central D-elements changes no action on D.

The additive Lie ring of P_i now splits canonically as

    L_i=Z_i⊕[L_i,B_i].                                (12)

Coprime averaging gives its fixed/moving decomposition; its fixed subgroup is Z_i because U_i has no B_i-fixed point. Thus (12) holds even if the initial additive extension over Z_i was nonsplit. Both S_i and τS_i lie in the moving part: a B_i-equivariant graph into fixed Z_i has zero map. They are invariant under A. Indeed C normalizes S_i, and τ(C) differs from C⁻¹ by elements of Z(D), centralizing D, so it also normalizes τS_i.

Their intersection is trivial. The full-inverted-set transversal gives H₀∩τH₀=C_{H₀}(τ), so S_i∩τS_i is pointwise τ-fixed. On that subgroup the actions of c and c⁻¹ agree; oddness makes the action of C trivial. Its shadow is therefore B_i-fixed, hence zero, and it lies in H₀∩Z_i=1. Because both subgroups lie in the same central-free splitting (12), their shadows are disjoint.

The actual group E₀ is the product of its Sylow groups E_i=Z_i⋊C_i, since the coprime center actions are trivial. Each E_i is τ-stable. Its full inverted set injects into E_i/C_i by the original transversal, so |A_i|≤|Z_i^{σ_i}|. Meanwhile W_i injects into U_i^τ, and inverse B_i-weight pairing on p-power layers gives |U_i^τ|²=|U_i|. The primewise fixed/stabilizer equality is

    |A_i||W_i|=|Z_i^{σ_i}||U_i^τ|.

Both inequalities are equalities. Consequently U_i=W_i⊕τW_i and |A_i|=|Z_i^{σ_i}|. This E_i injection is inside an actual subgroup of G, unlike an unjustified quotient-folder argument.

One also has Z_i=P_i′. In the additive abelianization of L_i, the B_i-fixed part is the image of Z_i. Since D=G′=[D,C]D′, that image is generated by A_i-displacements. Finite p-group Nakayama makes it zero. The reverse inclusion holds by class two. The C-action on D is faithful by H₀∩C_G(D)=1; (12) and bracket generation then make the combined R_i faithful. Identifying τW_i with a second copy of W_i gives exactly (1)–(2). We have obtained all the stated structural data.

It remains essential to recover the original loop, not merely a conjugate-stabilizer representative. Write its stabilizer as H=dH₀d⁻¹ with d∈D. There is a product-set factorization

    D=C_D(τ) Z^- S.                                  (13)

Indeed U=U^τ⊕W, because W⊕τW=U. Lift the fixed component to C_D(τ) using coprime fixed lifting, and lift the other component to S. The remaining center decomposes into Z^+⊕Z^−; absorb its positive part into C_D(τ). Thus d=c z s with c fixed by τ, z∈Z^- and s∈S. Conjugation by c preserves the full K and is an actual folder isomorphism. Conjugation by z preserves S and changes f to

    f_z(a)=f(a)+(1−T(a))z.                            (14)

This remains a cocycle and satisfies (3), because σz=−z implies σ(1−T(a))z=T(a)⁻¹(1−T(a))z. Therefore the original loop is isomorphic to data (1)–(4) with f_z. This argument neither drops the stabilizer position without accounting for it nor assumes that every isotope is isomorphic; that position is retained in the positive cocycle. Necessity of the finite tests follows from their exact derivations above. Exhaustion is proved under the cited inputs.

## Complete isomorphism relation and scope

Two selected data give isomorphic loops iff their prime sets agree and there are group isomorphisms

    E:A→A′,   L_i:W_i→W_i′,   M_i:Z_i→Z_i′

satisfying, for all i,a,x,y,

    M_iσ_i=σ_i′M_i,
    M_i b_i(x,y)=b_i′(L_i x,L_i y),
    L_i R_i(a)=R_i′(E(a))L_i,
    M_i T_i(a)=T_i′(E(a))M_i,
    M_i f_i(a)=f_i′(E(a)).                            (15)

These are finite abelian-group and bimap equations, not F_p-linear conditions unless the input groups are elementary. Sufficiency follows by applying (L_i,L_i,M_i) on D and E on A; (15) carries τ,H,K to their primed versions.

For necessity, a loop isomorphism induces a canonical group isomorphism preserving D=G′, each same-prime Sylow factor, H and τ (the latter is unique on the generating K). It preserves S=H∩D and τS. Since the additive decomposition is S⊕τS⊕Z, its Lie-ring restriction has exactly the form (L_i,L_i,M_i), with no central shear or mixing of the two axes. Let its induced quotient map be E and write the image of a∈A as v(a)E(a), v(a)∈D′. Preservation of the graph H and of Z(D) puts the vector part of v(a) in the first axis. The image of a is τ′-inverted, so (5) forces that vector part to vanish. Thus v(a) is central in D′, and group conjugation gives the action intertwining in (15).

The graph condition now says v(a)=f′(E(a))−M f(a). By (3) and the intertwining, this is in the positive eigenspace of T′(E(a))σ′. Inversion of v(a)E(a) puts it in the negative eigenspace of the same involution. Oddness makes their intersection zero. Hence v(a)=0 and the final equation of (15) follows. This accounts for all complement changes and stabilizer positions; it does not presuppose a G-loop property.

Every selected simple loop is nonassociative because the canonical stabilizer H is nontrivial, whereas a group's canonical left action is regular. If only proper/non-Moufang members are wanted, a finite Moufang-identity test on the constructed section selects exactly that subclass. No unproved assertion that every syntactic datum is proper is used. The existing simple-group and Moufang baselines are handled separately in the all-simple program.

At exact source `226a8dc1eb503026c350ffe3b7ac93da9077a593`, GPT-6.1 Terra reviewers [model reviewer identity omitted], [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the entire stated theorem under the cited coprime-center, faithful-action, odd-folder, class-two Lie-ring and strict-defect interfaces. Each checked construction and the quadratic image-set test, arbitrary-exponent generation, the complete normal-subgroup tuples including the central homomorphism u, the exact defect, Hall alignment and actual-subgroup order bounds, positive-cocycle normalization, preservation of the original loop through (13)–(14), and both directions of (15). They expressly retained the endpoint and did not infer a G-loop theorem, closed orbit census or global Bol classification. No computation, fresh primary-source audit, formal verification, literature novelty or manageable global bound is claimed. This is a structural parameterization of the entire stated class-two derived branch, not an assertion that all odd simple envelopes have class-two or even nilpotent derived group; higher classes already occur by the reviewed unbounded-class theorem.
