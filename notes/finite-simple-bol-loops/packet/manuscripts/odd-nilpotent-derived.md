# The nilpotent-derived odd-envelope route

This continuation belongs to 0323:C0010 [context outside this selected packet: `../claims/C0010.md`] and 0323.NONBRUCK_ODD, with the scoped independent reviews below. Its bounded question is whether the reviewed exclusion of metabelian canonical envelopes extends to envelopes whose derived subgroup is nilpotent. This would still be weaker than excluding all groups of Fitting height at most two: a nilpotent quotient by the Fitting subgroup need not be abelian. The deductions below restrict the case and refute a proposed group-theoretic shortcut. The later [cross-coupled construction](odd-cross-extraspecial.md), with independent reviews recorded there, now establishes that nilpotent derived groups with extraspecial Sylow factors do occur in simple proper odd loops. The remaining task is their structural classification, not universal exclusion.

Use a finite simple nonassociative odd-order left Bol loop Q with canonical faithful generating folder (G,H,K), inverting automorphism τ, D=G′ and A=G/D. The [derived-envelope deductions](odd-folder-radicals.md#derived-envelope-constraints-on-the-fixed-stabilizer) reviewed at `e896039d004ff3882621aca115b1a39cc8fed207` give G=HD, C_G(τ)≤D, |H|=|C_G(τ)|, and faithful transitivity of D. The general strict-defect input at `95f226ac6c02b0153f3c226d823518e0891c1f1d` gives |H∩L|<|C_L(τ)| for every nontrivial proper τ-stable normal L. Their oddness, inversion and source qualifications remain in the linked manuscript. Assume in the next two sections that D is nilpotent.

## Sylow restrictions and scalar inversion

Write D=∏_p D_p and S=H∩D=∏_p S_p, with S_p=H∩D_p. Each D_p is characteristic in D, hence normal in G and τ-stable. The subgroup core_{D_p}(S_p) is normalized by H, by D_p and by the other Sylow factors, so is normal in G=HD and contained in H. It is therefore trivial. In particular Z(D_p)∩S_p=1, and the center acts semiregularly on D_p/S_p. Thus

    |Q|=∏_p [D_p:S_p],       |Z(D_p)| divides [D_p:S_p].

This is an equality of cardinalities, not a product decomposition of Q. If D has class at most two, each S_p is abelian, since S_p′≤S_p∩Z(D_p)=1; this does not make S_p trivial.

The centralizer and stabilizer orders also give the exact identity

    |A|=|C_D(τ)|/|S|=∏_p |C_{D_p}(τ)|/|S_p|.

For every nonzero D_p the corresponding ratio is a positive power of p strictly greater than one, by strict defect (D_p<G because nontrivial solvable G has nontrivial abelianization). Also S_p<D_p by core-freeness. Consequently the prime-divisor sets satisfy

    π(G)=π(D)=π(A)=π(|Q|).

In particular, each prime occurring in the nilpotent derived subgroup must also occur in the abelian quotient. These sets contain at least two primes by C0011 [context outside this selected packet: `../claims/C0011.md`], proof §§1–2, scoped review `932ead5db5f39045e2085caa6b062f6b981b2813`. No bound on the number or powers of these primes follows.

Fix p and put V=D_p/Φ(D_p). The G-action on this elementary abelian group factors through the odd abelian group A, because D_p acts trivially and the other Sylow factors centralize D_p. The involution τ cannot commute with this A-action. Indeed τ induces inversion on A, so if it commuted, the compatibility identity τρ(a)τ⁻¹=ρ(a⁻¹) would give ρ(a)²=1; oddness forces the entire A-action to be trivial. Quotient G by N=Φ(D_p)∏_{r≠p}D_r. Its derived subgroup D/N≅V would then be central. Since G/N=(HN/N)(D/N), its derived subgroup would equal (HN/N)′ and lie in HN/N. Hence D_p=S_pΦ(D_p). A proper subgroup of a finite p-group lies in a maximal subgroup containing its Frattini subgroup, so this equality forces S_p=D_p, contradicting core-freeness.

Thus the action of A is nontrivial on every Sylow Frattini shadow, and τ is nonscalar there. This argument does not prove V=[V,A]: quotienting further by [V,A] only gives V=image(S_p)+[V,A], and core-freeness need not survive that quotient.

## An obstruction for every abelianization-surjecting stabilizer subgroup

This observation does not require D nilpotent. If C≤H maps onto nontrivial A=G/G′, then C and τ(C) cannot be G-conjugate. A conjugacy would produce an outside element normalizing C in G⋊⟨τ̂⟩. An odd power is an outside involution λ still normalizing C. By the same marked-class and Schur–Zassenhaus inputs as the reviewed H argument, λ lies in Λ=τ̂^G and C∩Λ²=1. Therefore c⁻¹c^λ=1 for each c∈C. But λ inverts A and C surjects onto A, contradicting its odd nontrivial order.

One proposed extension of the metabelian proof was to choose a minimal supplement C≤H to D and prove it conjugate to τ(C) using nilpotence of D. Such a C exists and maps onto A. Its intersection with D lies in Φ(C): otherwise a maximal subgroup missing some of that intersection would still supplement D, contradicting minimality. However the next explicit example shows that even a core-free complement to a nilpotent derived subgroup need not be conjugate to its involution image. A proof for Bol folders must use more of their hypotheses.

## Failure of the pure-group conjugacy shortcut

The following construction is a finite group with specified subgroups and an involution, **not a Bol folder**. Work over F₇ and let V=X⊕Y with dim X=dim Y=4 and alternating form

    ⟨(x,y),(x′,y′)⟩=xᵀy′−yᵀx′.

Let P=V×F₇ with product (v,z)(w,t)=(v+w,z+t+½⟨v,w⟩). Bilinearity gives associativity; its commutator form is the displayed nondegenerate form, so P has order 7⁹, exponent seven and Z(P)=P′={(0,z)}. Set

    T = [[0,1],[0,0]],
    J = [[0,I₂],[-I₂,0]],
    R = diag(T,Tᵀ),        B=I₄+R.

The block identities R²=0, Jᵀ=−J, J²=−I₄ and JRᵀJ⁻¹=R follow directly. Let u and a act on V by diag(2I₄,4I₄) and diag(B,B⁻ᵀ), respectively, fixing the central coordinate of P. These form-preserving maps commute, have orders three and seven, and give a faithful C₃×C₇ action. Set G_* = P⋊⟨u,a⟩. Since u−1 is invertible on V, the commutators with u project onto all of P/Z(P). Any subgroup surjecting onto this quotient contains P′ by nondegeneracy, and hence equals P. Thus G_*′=P.

The linear involution t(x,y)=(Jy,J⁻¹x) preserves the alternating form. It conjugates the actions of u and a to their inverses: for a this follows from JB⁻ᵀJ⁻¹=B⁻¹ and J⁻¹BJ=Bᵀ. Therefore it defines an involution τ_* of G_* that fixes Z(P) and sends u↦u⁻¹, a↦a⁻¹. In particular τ_* inverts G_*/P.

Write z=(0,1) for a generator of Z(P), and for s∈F₇ put C_s=⟨u,az^s⟩. Each C_s≅C₃×C₇ maps isomorphically to G_*/P and is a minimal supplement with C_s∩P=1. It is core-free: its normal core would commute with P because its commutators with P lie in the trivial intersection C_s∩P; the induced C_s-action on P is faithful, so that core is trivial. Also τ_*(C_s)=C_{−s}.

The seven complements C_s are pairwise nonconjugate. Their unique subgroups of order three are all ⟨u⟩. If g=pc, p∈P and c∈⟨u,a⟩, conjugates one C_s to another, it must centralize u: the image of u in the abelian quotient G_*/P fixes its choice inside ⟨u⟩. Since c centralizes u, we have p∈C_P(u)=Z(P), using the absence of nonzero u-fixed vectors in V. Both p and c then centralize u, a and z, so cannot change C_s. In particular C₁ and τ_*(C₁)=C_{−1} are not conjugate, despite core-freeness, nilpotent G_*′, and trivial intersection with G_*′.

The missing Bol condition is already visible numerically. Since τ_* inverts the odd quotient, C_{G_*}(τ_*)=C_P(τ_*). The fixed space of t on V has dimension four, and τ_* fixes the central coordinate, giving |C_{G_*}(τ_*)|=7⁵. This is different from |C_s|=21. The canonical odd Bol-folder equality |H|=|C_G(τ)| therefore fails. The example refutes only the proposed pure-group conjugacy shortcut; it is neither a loop construction nor evidence against a nilpotent-derived exclusion for simple Bol loops.

## Extraspecial Sylow factors: exponent and module restrictions

**Deduction with the scoped independent reviews below.** Let Q be a finite simple nonassociative odd-order left Bol loop, (G,H,K) its canonical folder and τ its inverting involution. Assume D=G′ is nilpotent, and its nontrivial Sylow p-factor P is extraspecial. Put Z=Z(P)=P′=Φ(P), U=P/Z, A=G/D and S=H∩P. Then:

* Z≤Z(G), τ fixes Z pointwise, and the commutator form makes U a symplectic F_p A-module. The induced τ is a symplectic involution σ implementing inversion on A.
* U has no trivial F_p A-composition factor. Every simple F_p A-composition factor occurs with even multiplicity, including without a semisimplicity hypothesis. In particular dim_Fp U is divisible by 4, so |P|=p^{1+4m} for some m≥1.
* P has exponent p. Thus the full K² argument below applies to every surviving extraspecial factor.
* W=SZ/Z is an A-invariant totally isotropic subspace with W∩σW=0. Writing U− for the negative σ-eigenspace, the full marked-transversal condition forces W∩gU−=0 for all g∈G. In particular (H∩τH)∩P=1. These conditions do not exclude W=0 or all admissible reducible U.

The nontrivial central subgroup Z prevents an intrinsic exact-factorization witness, by the reviewed odd center obstruction in [the criterion](exact-factorization-criterion.md#bruck-stabilizers-and-necessary-witness-tests). The later cross-coupled family realizes this regime and refutes exact-factorization exhaustiveness. The restrictions in this section remain necessary conditions and do not themselves classify the surviving factors.

Proof. Z is characteristic in P, P in nilpotent D, and D in G. The strict-defect theorem rules out τ inverting the nontrivial normal subgroup Z, so τ fixes Z pointwise. D centralizes Z, and conjugation on Z therefore factors through A. Since τ induces inversion on A and fixes Z, conjugation by a and by a^−1 has the same effect on Z; oddness makes this action trivial. Thus Z≤Z(G). The commutator form ω:U×U→Z≅F_p is A-invariant and σ is symplectic with σaσ^−1=a^−1. Core-freeness gives S∩Z=1, so S is abelian and W embeds in U as an isotropic subspace. S is H-normalized; P acts trivially on U and other Sylow factors of D centralize P, so G=HD makes W A-invariant.

We first prove U has no trivial A-composition factor. Let B=A_{p′}, R=A_p and M=U^B. Since B acts with order prime to p, averaging gives an A-stable decomposition U=M⊕[U,B], and M is nondegenerate for ω. Let W0=W∩M; it is isotropic and R-invariant. The identity U=W+[U,A] follows by projecting G′=[HD,HD] onto P/Φ(P): [H,H] maps into W, [H,D] maps into [U,A], and [D,D] maps trivially. Applying the B-averaging projection gives M=W0+[M,R]. The p-group R cannot act on a nonzero F_p-space with zero coinvariants: its augmentation ideal is nilpotent. Applied to M/W0, this forces M=W0. A nondegenerate symplectic space cannot be isotropic, so M=0. As B has p′-order and its invariants functor is exact, no simple A-composition factor of U is trivial.

For even multiplicities, extend scalars to an algebraic closure k and consider Γ=A⋊⟨σ⟩, with σ inverting A. The normal p-subgroup A_p acts trivially on each simple kΓ-module. The quotient Γ/A_p has order prime to p; its simple modules are the two one-dimensional σ=±1 modules with trivial A-character, and the two-dimensional χ⊕χ^−1 modules for nontrivial characters χ of A_{p′}, with σ swapping the lines. Since A is odd, χ≠χ^−1. Each simple is self-dual, admits an invariant symmetric form and admits no invariant alternating form. For any simple Γ-submodule T of k⊗U, the alternating form therefore vanishes on T. Removing T and its dual T* via T⊥/T preserves a nondegenerate alternating Γ-form; induction shows every simple Γ-composition factor appears an even number of times. Restriction to A and Frobenius descent give even multiplicity for every simple F_p A-factor, without assuming U semisimple. Nontrivial dual A-character orbits are either distinct paired orbits, contributing a multiple of four, or self-dual orbits of even degree, each of even multiplicity; because the trivial orbit is absent, dim U is divisible by 4.

For the exponent, class two and odd p give a linear p-th-power map U→Z: (xy)^p=x^p y^p because [y,x] has exponent p and binom(p,2) is divisible by p. It is A-equivariant because Z is central in G. The target is a trivial A-module, so any nonzero map would yield a trivial A-composition factor of U. Therefore it vanishes and P has exponent p.

For the full transversal, use the class-two exponent-p group/Lie correspondence, obtained here by replacing the product with its correction by one half of the central commutator. This gives an F_p-vector space with bilinear bracket, preserved by τ. Choose a τ-stable linear complement to Z by averaging, and identify P with the resulting BCH group U⊕Z. The multiplication is (u,z)(v,t)=(u+v,z+t+ω(u,v)/2), τ acts by (σu,z), and σ's negative symplectic eigenspace U− is nondegenerate. For any nonzero v∈U− and any z∈Z, choose u∈U− with ω(u,v)/2=z. Then (v,z)=(u,0)(v−u,0) belongs to K², since both factors are τ-inverted. K² is G-conjugacy invariant and H∩K²=1. Therefore W avoids every gU−. In particular W∩U−=0.

The intersection W∩σW is A- and σ-stable. It is disjoint from U−, so σ fixes it pointwise. Since σ conjugates the A-action to its inverse and A is odd, A acts trivially on it. But U has no trivial A-composition factor, so W∩σW=0. An element of B0=(H∩τH)∩P is fixed by τ and projects into W∩σW; as H∩Z=1 it is 1.

Finally, this within-P full-K² constraint has a precise limitation. Because Z≤Z(G), nontrivial central elements are not in K². Conversely, for x∈K²∩P, write x=λλ′ with marked involutions λ,λ′; then λ′=λx forces x to be inverted by λ, so its shadow lies in a G-conjugate of U−. The central-fiber calculation gives the reverse inclusion for nonzero shadows. Hence
 K²∩P={1}∪{x∈P:xZ≠0 lies in ⋃_{g∈G}gU−}.
Since W is G-invariant, avoiding all these conjugates is equivalent to W∩U−=0. Therefore further use of full transversal geometry must involve K² elements outside P or additional stabilizer/cocycle constraints; these arguments do not establish a general extraspecial exclusion.

Inputs: odd-folder-radicals.md reviewed strict-defect and derived-envelope results; exact-factorization-criterion.md reviewed center obstruction; odd-nilpotent-derived.md reviewed Sylow and scalar-shadow results; C0001/C0007 canonical-folder and marked-class inputs; FKP arXiv:math/0208231v2 Proposition 6.1 and Theorem 4.14. Exact source and review pins are recorded in those files. The scoped independent reviews of this deduction are recorded below; no computation or formal verification is claimed.

## Remaining obligation and evidence

The cross-coupled family now supplies surviving nilpotent D. The remaining question is to classify all admissible nilpotent-derived folders using the full inverted section and its transversality; no necessity theorem for that family is established. Neither a quotient of a core-free group action nor a nilpotent supplement automatically supplies the missing loop quotient or conjugacy. The control uses explicit matrix identities and finite-group calculations, not a computational search.

GPT-6.1 Terra reviewers [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted this manuscript at exact source `27e40560748edba10af80088d99264cd25fab1d5`, conditional on the cited odd-folder, strict-defect, derived-envelope and C0011 inputs. They checked the Sylow/core and prime-support assertions, the nonscalar Frattini-action argument, and the subgroup nonconjugacy extension. They checked the explicit block matrices, extraspecial group, core-free pairwise nonconjugate complements, inversion action and mismatched centralizer order in the control. Neither review uses a computation or formal verification, proves a nilpotent-derived exclusion, or treats the control as a Bol folder.

At exact source `6033272fbbd42f39c07ae59808ca122c9d60348e`, GPT-6.1 Terra reviewers [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the extraspecial Sylow-factor section, conditional on the cited canonical-folder, strict-defect, derived-envelope and marked-class inputs. Both checked the centrality argument, the necessary H′ contribution to U=W+[U,A], averaging and p-group coinvariants, the nonsemisimple generalized-dihedral multiplicity proof, the exponent deduction and the exact BCH/marked-section formula. They accepted the disjoint stabilizer shadows and the explicitly limited scope. Their reviews neither reprove all upstream results nor exclude nilpotent derived groups or every extraspecial factor. No computation or formal verification was used.

## Fixed-point obstruction on every derived Sylow factor

**Continuation of 0323:C0010, with the scoped independent reviews below.** Let Q be a finite simple nonassociative odd left Bol loop with canonical (G,H,K,τ), and assume D=G′ is nilpotent. Put A=G/D. For every nontrivial Sylow p-factor P of D, let D_{p′} be the product of the others and B=A_{p′}. In G/D_{p′}, choose a complement B₀ to P in the inverse image of B. Such complements exist and are P-conjugate by Schur–Zassenhaus. The claimed necessary condition is

    C_P(B₀)≠1.                                         (12)

This does not assume class two, exponent p, center centrality or a split original envelope. The coprime action is specified through the actual local complement; (12) is independent of its choice. The inputs are the reviewed odd full marked transversal and prime-support/no-normal-Hall results linked above, and the Schur–Zassenhaus version recorded in REFERENCES.md. The precise remaining gap is classifying the folders that satisfy (12), rather than mistaking this obstruction for exhaustion.

Suppose instead C_P(B₀)=1. Set Ḡ=G/D_{p′} and E=Ḡ⋊⟨τ̂⟩. The inverse image of B is normal in E, and all its Hall complements are P-conjugate. Thus E=P N_E(B₀). Its normalizer kernel in P is C_P(B₀)=1: an element of P normalizing B₀ has commutators with B₀ in P∩B₀. Consequently N_E(B₀) maps isomorphically onto A⋊⟨τ̂⟩. It supplies a pure complement A₀ in Ḡ and an outside involution λ̄ normalizing and inverting A₀.

The image H̄ of H maps onto A, with kernel S=H̄∩P. A Hall complement over B inside H̄ can be P-conjugated to B₀; make that actual conjugation of H in G, retaining the fixed original K. Its full-conjugate transversal property is preserved. A second Hall-complement normalizer argument, this time inside H̄ with C_S(B₀)=1, shows H̄∩N_Ḡ(B₀) maps onto A. Since N_Ḡ(B₀) already maps isomorphically to A, it equals A₀ and lies in H̄.

The reviewed prime-support result gives A_p≠1. Choose a nonidentity p-element h̄∈A₀ and lift it to a p-element h∈H. Sylow theory supplies such a lift, and the map on its cyclic subgroup is injective because the kernel lies in D_{p′}. Lift λ̄ to an outside involution λ in G⋊⟨τ̂⟩: the inverse image of ⟨λ̄⟩ has odd kernel, and an odd power of a lift of λ̄ is an involution mapping to it. This λ normalizes L=⟨h⟩D_{p′} and induces inversion on L/D_{p′}. The subgroups ⟨h⟩ and λ⟨h⟩λ are complements to the normal Hall p′-subgroup D_{p′} inside L. Schur–Zassenhaus conjugates them by D_{p′}. After that adjustment, an odd power gives an outside involution normalizing ⟨h⟩ and acting there by inversion, since the cyclic subgroup injects into L/D_{p′}. All outside involutions belong to the original marked class Λ. Thus h∈Λ²=K², contradicting h∈H and h≠1. No projected quotient loop has been assumed. This proves (12), subject to independent review of this new application.

A useful centerless consequence follows. If Z(G)=1, then Z(P)^{B₀}=1 for every P. Otherwise its subgroup of elements of order dividing p contains a nonzero B-fixed vector; the commuting p-group A_p acting on this vector space has a nonzero fixed vector. D centralizes Z(P), so this gives a nonidentity element of Z(G), contradiction. Coprime fixed-point lifting in P→P/Z(P), together with (12), therefore gives

    Z(P)^{B₀}=1,   (P/Z(P))^{B₀}≠1.                    (13)

In the class-two case the second group is an abelian p-group, identifying the unclassified centerless branch as one with fixed quotient elements but no fixed central elements. In the reviewed central-center branch, by contrast, the quotient has no B-fixed elements and the entire center is fixed. Conditions (12)–(13) neither assert that a centerless simple example exists nor exclude it. At exact source `2c55b3347a1b65d9475902db9575bf6647431fb2`, GPT-6.1 Terra reviewers [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted this subsection. Both checked the two Hall-normalizer arguments, actual stabilizer conjugation, cyclic p-element lift, outside-involution lift and correction, and the centerless corollary. Their acceptances retain the pinned prime-support, marked-transversal and Schur–Zassenhaus inputs. No computation, formal verification or novelty claim is made.
