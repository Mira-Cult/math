# An intrinsic criterion for simple exact-factorization folders

This manuscript-local lemma has received scoped independent model review as recorded below; it is not a new permanent claim. The folder conventions are those of `0323-finite-simple-non-moufang-bol-loops:C0001`, especially its Theorems 1.3–1.4. The exact-factorization construction is Nagy, *A class of simple proper Bol loops*, arXiv:math/0703919v1, Proposition 3.2; see also `0323-finite-simple-non-moufang-bol-loops:C0002`, Proposition 1.1. The source examined for the repository claims and proofs is commit `79b70a50b19bc728b349a2a6ed2bd958391e8b6e`. No status label on those claims is assumed to constitute independent review.

This argument develops the normal-subgroup route in C0010 [context outside this selected packet: `../claims/C0010.md#proof`]; it is not a new permanent claim ID.

## Lemma (simple exact-factorization criterion)

Let Q be a finite simple **nonassociative** left Bol loop. Let G be its faithful left multiplication group, H the stabilizer of its identity, and K its set of left translations; thus G=⟨K⟩, 1∈K, K is a transversal to the left cosets gH, and |G|=|H||K|. Let τ∈Aut(G) satisfy τ(k)=k⁻¹ for every k∈K. Such a τ exists and is unique: the standard twisted-subgroup argument is written in `0323-finite-simple-non-moufang-bol-loops:C0007`, proof, Theorem 1.1(1), using the triviality of the left nucleus for a simple nonassociative left Bol loop; see also `C0001`, proof, Theorem 1.5(1). Here “involutory” means τ²=1 and includes τ=1.

Then Q is isomorphic to the loop of some finite exact group factorization X=Y₀Y₁, Y₀∩Y₁=1, by Nagy's construction if and only if there is a normal subgroup N◁G with

    N∩τ(N)=1,     [G:N]=|K|,     HN∩Hτ(N)=H.                 (*)

Moreover, for each such N one can take X=G/N, with factors the two coordinate projections of H under the embedding in the proof. In this simple nonassociative setting both factors are nontrivial and core-free. This is an existence criterion, not a classification of all possible witnesses N or an isomorphism criterion for different factorizations.

### Proof: sufficiency

Write N^τ=τ(N), X=G/N, and define

    ι:G → X×X,       g ↦ (gN,τ(g)N).

Its kernel is N∩N^τ=1. For k∈K, ι(k)=(x,x⁻¹) where x=kN. If kN=lN, then k⁻¹N=l⁻¹N, so ι(k)=ι(l), hence k=l. Since |K|=[G:N]=|X|, ι maps K bijectively to

    S={(x,x⁻¹):x∈X}.

Thus ι(G)=⟨S⟩. Explicitly,

    ⟨S⟩ = F := {(u,v)∈X×X : uv∈X′}.

Indeed, F is the kernel of (u,v)↦uvX′ into the abelianization X/X′, and S⊆F. Conversely, (x,x⁻¹)(y,y⁻¹)(xy,(xy)⁻¹)⁻¹=(1,x⁻¹y⁻¹xy), so 1×X′≤⟨S⟩; coordinate swap preserves S, so X′×1≤⟨S⟩ as well. For uv∈X′, (u,v)=(u,u⁻¹)(1,uv)∈⟨S⟩. In particular |G|=|X||X′|, and |H|=|X′|.

Identify G with F and put Y₀=pr₁(H), Y₁=pr₂(H). The kernels of the two coordinate projections on G are N and N^τ respectively. Consequently the inverse images of Y₀ and Y₁ in G are HN and HN^τ. The last condition in (*) says precisely

    H = F∩(Y₀×Y₁).                                         (1)

If x∈Y₀∩Y₁, then (x,x⁻¹) lies in S∩(Y₀×Y₁)=K∩H={1}. Hence Y₀∩Y₁=1.

Let A=X/X′ and let D₀,D₁ be the images of Y₀,Y₁ in A. Since H is a subgroup of F and projects onto each Yi, the relation uvX′=1 shows D₀=D₁=:D. Equation (1) identifies H with the full fiber product of Y₀ and Y₁ over A, with inverse matching. Therefore

    |H| = |Y₀||Y₁|/|D|,  so  |Y₀||Y₁|=|X′||D|.             (2)

It remains to show D=A. Let M be the inverse image of D in X. The map f:Q→X/M given by f(k)=xM for ι(k)=(x,x⁻¹) is a loop homomorphism. To see this explicitly, if the product of the loop elements corresponding to k,l∈K corresponds to m∈K, then kl∈mH by the definition of the folder product. Projecting to X and then X/M gives f(k)f(l)=f(m), since the first projection of H is Y₀≤M. It is surjective because K→X is bijective.

If X′=1, then F=S is an abelian group and H=1, so the folder loop is an associative group, contrary to hypothesis. Thus X′≠1. If D<A, then M<X and the surjective homomorphism f has a nontrivial proper kernel: its kernel contains the |X′|>1 elements indexed by X′, and its image is nontrivial. This contradicts simplicity. Thus D=A, and (2) yields |Y₀||Y₁|=|X|. Together with Y₀∩Y₁=1, this proves X=Y₀Y₁ is an exact factorization.

By (1), ι identifies (G,H,K) with the generated folder (F,F∩(Y₀×Y₁),S) of this factorization. Both folders have the same transversal multiplication, so the reconstructed loop is Q. Both factors are nontrivial: if either were 1, the exact-factorization folder product is associative (equivalently, the other factor is X and the product can be checked directly). Core-freeness follows from the necessity argument below.

### Proof: necessity

Suppose Q arises from a finite exact factorization X=Y₀Y₁, Y₀∩Y₁=1, using S={(x,x⁻¹)}. Put F=⟨S⟩ and J=F∩(Y₀×Y₁). As just proved, F={(u,v):uv∈X′}, and |J|=|X′| because S is a transversal to J in F. Both Yi are nontrivial, since a trivial factor gives an associative group loop.

The construction is meaningful even before imposing core-freeness. For any exact factorization X=Y₀Y₁, also X=Y₁Y₀. For z∈X write z=b a with b∈Y₁ and a∈Y₀; then Y₀∩z⁻¹Y₁z=a⁻¹(Y₀∩Y₁)a=1. If (x,x⁻¹) and (z,z⁻¹) occupy the same left coset of Y₀×Y₁, then z⁻¹x∈Y₀∩z⁻¹Y₁z, so x=z. Counting shows S is a transversal, since [X×X:Y₀×Y₁]=|X|. It is inverse-closed and closed under s t s, so the folder criterion in C0001 gives a Bol loop, and restricting to F leaves its operation unchanged. Thus this paragraph applies equally to the exact quotient factorization used next. Faithfulness is needed only to identify the generated action group with the canonical multiplication group, not to construct the loop.

First, each Yi is core-free. If 1≠C=Core_X(Y₀), the natural quotient maps the exact factorization X=Y₀Y₁ to an exact factorization X/C=(Y₀/C)(Y₁C/C): the two image factors intersect trivially, since C≤Y₀ and Y₀∩Y₁=1. Coordinate quotient maps S onto the corresponding transversal and J into its stabilizer, so it induces a loop homomorphism onto the quotient construction. It is surjective with kernel of size |C|>1; its image has size |X/C|≥|Y₁|>1, contrary to simplicity. The argument for Core_X(Y₁) is symmetric.

Next X′Y₀=X and X′Y₁=X. For example, if M=X′Y₀<X, then M is normal and contains Y₀; the condition uv∈X′ shows both projections of J lie in M. Projecting the folder multiplication onto X/M gives a surjective loop homomorphism Q→X/M. Its image is nontrivial and its kernel contains Y₀, which is nontrivial, contradicting simplicity. The other factor is symmetric.

These equalities imply prᵢ(J)=Yᵢ: for y₀∈Y₀, write y₀⁻¹∈X′Y₁ and select y₁∈Y₁ with y₀y₁∈X′, and similarly for the other projection. Let C=Core_F(J). For each i, prᵢ(C)≤Yᵢ is normalized by prᵢ(F)=X, hence lies in Core_X(Yᵢ)=1. So C=1, and (F,J,S) is the faithful folder (G,H,K).

Coordinate swap on F inverts S, so by uniqueness it is τ. Set N=X′×1≤F. It is normal in F, τ(N)=1×X′, their intersection is 1, and [F:N]=|X|=|S|. Finally JN and Jτ(N) are the inverse images in F of Y₁ under pr₂ and Y₀ under pr₁ respectively. Since J=F∩(Y₀×Y₁), their intersection is J. Thus (*) holds. ∎

## Scope check: exponent 2

If Q has exponent 2, then every left translation k satisfies k²=1 by the left inverse property for Bol loops. Hence τ fixes every element of K, and τ=1 because K generates G. If (*) held, N∩τ(N)=N would force N=1, and [G:N]=|K| together with |G|=|H||K| would give H=1. Then K=G, so Q is a group. Therefore no nonassociative exponent-2 left Bol loop satisfies (*).

This excludes the criterion as a route to exhaustiveness of the entire target class: Nagy, *A class of finite simple Bol loops of exponent 2*, arXiv:0709.4544v1, Theorem 3.6 and §5 (in particular Proposition 5.1 and Theorem 5.2), constructs finite simple nonassociative right Bol loops of exponent 2; taking opposites gives left Bol examples. This conclusion does not require the separate isotopy census in `C0012`.

Outside the simple nonassociative hypotheses, the construction in the sufficiency proof need not extract an exact factorization from a given witness: for a nontrivial finite abelian group folder (G,H,K)=(A,1,A), inversion τ and N=1 satisfy (*), while the extracted factors are both trivial. This example does not refute the existence of some other exact-factorization presentation of the group loop.

## Bruck stabilizers and necessary witness tests

**Scoped independent review of these deductions is recorded below.** Retain the finite simple nonassociative canonical-folder hypotheses above, including the unique inverting automorphism τ of order at most two. Then Q is Bruck, meaning that inversion satisfies (xy)⁻¹=x⁻¹y⁻¹, if and only if τ(H)=H.

Indeed, if τ(H)=H, the well-defined permutation I:gH↦τ(g)H sends kH to k⁻¹H for every k∈K, so it is loop inversion. It conjugates each left translation L_x to L_{x⁻¹}, giving I(xy)=x⁻¹I(y). Conversely, the automorphic inverse property makes inversion normalize G and conjugate each L_x to L_{x⁻¹}; uniqueness identifies this action with τ, and inversion fixes the identity, so it preserves H. This is an isomorphism-invariant division of the target, not a classification of either part. If G is additionally primitive and τ(H)≠H, maximality of H gives ⟨H,τ(H)⟩=G.

Any witness N in (*) necessarily gives |H| dividing |Q|. In fact |N|=|H| and the disjoint normal subgroups N,τ(N) have product of order |H|², which divides |G|=|H||Q|. This is only a necessary test for membership in the exact-factorization family.

Now additionally suppose |Q| is odd. The source application and reviewed central constraint in [odd-folder-radicals.md](odd-folder-radicals.md#source-application-to-odd-order-loops) give |G| odd and τ fixes Z(G) pointwise. If a witness N exists, the proof above identifies G with F={(x,y)∈X²:xy∈X′} and K with {(x,x⁻¹):x∈X}. For z∈Z(X), the element (z,z⁻¹) lies in both K and Z(F). It is inverted by τ because it lies in K and fixed by τ because it is central. Odd order forces z=1. Both projections F→X are onto, so Z(F)≤Z(X)²=1; therefore Z(G)=1. Independently of the witness, τ induces inversion on G/G′ because it inverts the generating set K. Its pointwise action on Z(G) therefore gives Z(G)≤G′. A hypothetical odd simple folder with |H| not dividing |Q| or with nontrivial Z(G) would refute exact-factorization exhaustiveness. Neither such an example nor the converse is proved here.

## Bruck isotopy as a stabilizer-conjugacy test

**Deduction with the scoped independent reviews below.** Retain a finite simple nonassociative left Bol loop Q and its canonical (G,H,K,τ). In E=G⋊⟨t⟩ let t be the formal involution inducing τ, including when τ=1, and put Λ=tK. The following are equivalent:

1. Q is isotopic to a left Bruck loop.
2. H and τ(H) are conjugate in G.
3. Λ meets N_E(H).
4. Λ meets C_E(H).

Here isotopy means an arbitrary loop isotopy, not just an isomorphism or a quotient. The general principal-isotope calculation is [C0012, proof of Theorem 1.2(1)](../proofs/C0012.md); C0012 has unreviewed aggregate metadata, so the precise needed calculation is included here for separate review. For any left Bol loop, the Bol identity gives the autotopism (L_aR_a,L_a⁻¹,L_a). The principal product x∘y=R_a⁻¹(x)*L_b⁻¹(y), under the change X=L_a(x), Y=L_a(y), becomes

    X ⊙ Y = X * L_d⁻¹(Y),       d=a*(b*a),  L_d=L_aL_bL_a.

Every loop isotope is isomorphic to a principal isotope: from an isotopy (α,β,γ), transport the target along γ and use the target identity to express α,β as the corresponding original right and left translations. For the displayed product the identity is d, the left-translation set is Kk⁻¹ with k=L_d, and its generated group is G (the shifted set contains k⁻¹, and multiplying back recovers K). Its stabilizer is kHk⁻¹. Conjugating by k⁻¹ gives the faithful folder (G,H,k⁻¹K). Conversely every k∈K occurs by taking a to be the original identity and b the element with translation k. The shifted set is twisted: inverse closure and xyx closure follow directly by applying those properties to K. It is a transversal to the conjugates of H, since the untransported isotope is a loop and its displayed twisted generating translation set gives its Bol folder.

Simplicity persists under this operation: for an arbitrary principal isotope the generated left and right multiplication groups on the underlying set equal the original respective groups, since their translation sets are K L_b⁻¹ and the analogous right shift by R_a⁻¹; hence the full multiplication group and its primitivity are unchanged. An isotope of a group is isomorphic to a group, as follows immediately by rescaling its principal product; thus nonassociativity also persists. Consequently the canonical simple-folder inversion and Bruck-stabilizer test apply to each shift.

The automorphism τ_k=Inn(k⁻¹)∘τ has square one and inverts k⁻¹K: for a∈K,

    τ_k(k⁻¹a)=k⁻¹τ(k⁻¹a)k=a⁻¹k.

It is therefore the unique inverting automorphism of that shifted folder. By the Bruck-stabilizer equivalence above, the shift is Bruck exactly when τ_k(H)=H, or equivalently τ(H)=kHk⁻¹. Since every g∈G has the form kh with k∈K and h∈H, any conjugator for H can be replaced by such a k. This proves (1)⇔(2). The element λ=tk=k⁻¹t induces τ_k, giving (1)⇔(3). Finally a λ∈Λ normalizing H centralizes it: for h∈H, h⁻¹h^λ=(λ^h)λ belongs to H∩Λ²={1}, by the C0007 marked-class identity and conjugacy invariance of Λ. This proves (3)⇔(4). The normalizing involution must belong to the actual marked section Λ; an arbitrary involution of E is not sufficient.

For any τ-stable normal subgroup N◁G, nonconjugacy of HN/N and τ(H)N/N in G/N obstructs Bruck isotopy. Absence of any element of the projected Λ centralizing HN/N is another obstruction. Neither statement assumes that the projected section is a transversal or defines a quotient loop. The abelianization alone cannot give the nonconjugacy obstruction, since τ inverts G/G′ and therefore preserves the image of every subgroup H there.

### Disjoint known construction routes and the exact gap

A simple nonassociative exact-factorization loop has no Bruck isotope. Indeed the faithful representation above gives G≤X×X, τ as coordinate interchange, and projections of H equal to Y₀,Y₁. If H and τ(H) were G-conjugate, Y₀ and Y₁ would be X-conjugate. But in an exact factorization X=Y₀Y₁ the two factors intersect every conjugate of one another trivially: writing z=ba with b∈Y₁,a∈Y₀ gives Y₀∩z⁻¹Y₁z=a⁻¹(Y₀∩Y₁)a=1. Conjugacy would then force Y₀=1, contrary to the nonassociative hypotheses. This is a direct group argument and does not require the aggregate G-loop theorem in C0012. The reviewed odd-envelope nonconjugacy theorem at `e896039d004ff3882621aca115b1a39cc8fed207` similarly shows that every odd-order simple nonassociative Bol loop lies outside the Bruck-isotopy class.

The criterion gives a uniform extension of any Bruck construction scheme: apply the shifts (G,H,k⁻¹K), k∈K, and use the canonical folder-isomorphism criterion to identify duplicates. This covers all loops isotopic to the Bruck loops in that scheme. It does not classify the Bruck bases or the loops without a Bruck isotope, and different Bruck bases may themselves be isotopic.

For the **proper/non-Moufang** classification target 0323.CLASSIFY, the proposed disjunction “exact-factorization loop or Bruck isotope” is therefore equivalent to the following precise implication: if H and τ(H) are not G-conjugate, then a normal subgroup N satisfying (*) exists. The implication is now refuted by the [cross-coupled extraspecial construction](odd-cross-extraspecial.md), independently accepted at `62978672415973eb0f8043c6976d06b317a52d42` under its stated dependencies: its simple proper folder satisfies nonconjugacy but has no witness (*). The non-Moufang restriction here is essential; this proposed disjunction is not asserted for the simple Moufang baseline. The separate construction-parameter classifications remain useful, but they do not exhaust the target.

### Imprimitivity of both construction routes

This additional deduction has the scoped independent reviews below. A finite simple nonassociative Bruck loop has imprimitive one-sided multiplication group, and so does every loop isotope of it. To see this, transport left/right conventions by the opposite loop and use the same faithful action. The Baumeister–Stein structure and fiber inputs recorded in the all-radical scheme [context outside this selected packet: `bruck-all-radical-parameterization.md`], with scoped source audit and review at `6b719ad3026522f93cd9e0e027ae4027f6ee12df`, give P=O₂(G), G/P=∏ᵢPGL₂(qᵢ), and HP/P a product of proper point Borels. The odd-order Bruck solvability and decomposition place the simple nonassociative loop in the 2-power-exponent part. The number of factors is positive: with none, G=P and |Q| is a power of two, contrary to C0011 [context outside this selected packet: `../claims/C0011.md`], proof §§1–2, scoped review `932ead5db5f39045e2085caa6b062f6b981b2813`.

Also P≠1. If P=1, then n₀=[P:P∩H]=1 and the positive singleton-coordinate fiber formula in the cited scheme, equation (3), requires the cardinality 2/(qᵢ−1), which is not an integer for any allowed qᵢ≥5. Core-freeness of H now gives P⊄H, while the proper Borel product gives HP<G. Thus H<HP<G, proving imprimitivity. The principal-isotope reduction above preserves the action (G,G/H) after transport, so all isotopes have the same conclusion. This is a statement about the one-sided multiplication group, not the full multiplication group, which is primitive for a simple loop.

The exact-factorization route is likewise imprimitive directly from (*): N≠1 because otherwise H=1 and the loop is associative; core-freeness gives N⊄H; and HN<G because its image is one of the proper factors Yᵢ under the coordinate projection. Hence H<HN<G. Therefore the proposed two-family exhaustiveness for simple **proper** Bol loops would imply nonexistence of primitive one-sided multiplication groups in that class. No converse is proved. A proper simple Bol loop with primitive LMlt would simultaneously lie outside both routes and refute that proposed exhaustiveness.

## Remaining obligation

The lemma gives an intrinsic membership test for one construction family and supplies its associated data. It does not classify the loops in that family, decide when different witnesses or factorizations give isomorphic loops, or classify folders with no witness N. The latter include nonassociative exponent-2 examples, and unrestricted `0323.CLASSIFY` remains open. The proof relies on the specifically invoked folder/nucleus and inversion results; neither its scoped review nor its conclusion certifies the complete upstream claims.

## Independent review

GPT-6.1 Terra reviewer [model reviewer identity omitted] accepted the argument at exact source revision `e3a39be22fe1390d3717bdeee8f81d82f6817aef` after requesting correction of the Nagy proposition number and an explicit nonfaithful-transversality argument at the earlier revision `a4e8861e0355ee90e1ad7277f4aae21357622b6f`. The reviewed scope includes the generated subdirect group, both directions, quotient maps, core-free reduction and exponent-2 obstruction. The reviewer relies on the invoked parts of C0001 and C0007 and did not certify those full claims, a global classification, or formal verification. A second independent GPT-6.1 Terra reviewer, [model reviewer identity omitted], found no mathematical flaw at `a4e8861e0355ee90e1ad7277f4aae21357622b6f`, with the same dependency limits and without a source audit. This later paragraph records those reviews; it is not part of their examined source.

At exact source `d9bc55095490d42e41c359bbb88b67c78f6d4998`, GPT-6.1 Terra reviewer [model reviewer identity omitted] accepted the new Bruck-stabilizer and necessary-witness section, conditional on the prior intrinsic-criterion review, invoked C0001/C0007 inversion facts and reviewed odd-envelope results. The review covers the Bruck equivalence, primitive consequence, witness divisibility, witness centerlessness for odd Q, and the general odd-order inclusion Z(G)≤G′. It also accepted the disjoint/exhaustive branch division in PROBLEM.md without asserting family exhaustiveness, and directly checked Baumeister–Stein's decomposition source. The exponent-4 example remains source-reported MAGMA verification; the reviewer did not reproduce it or reprove the finite simple Moufang classification or all upstream claims.

At exact source `ea836a5f328d6bc52913aac8fd1841a87072f5f8`, GPT-6.1 Terra reviewers [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the Bruck-isotopy/conjugacy/marked-centralizer equivalence and its stated construction-route consequences. Both checked the inline arbitrary principal-isotope calculation, preservation of simplicity and nonassociativity, and the shifted inverting automorphism, without assuming acceptance of the C0012 aggregate. They checked the quotient obstructions without quotient-folder assumptions, separation of simple nonassociative exact-factorization loops from Bruck isotopes, and the explicit proper/non-Moufang scope of the remaining two-family implication. Their reviews retain the invoked C0001/C0007 and earlier intrinsic-criterion dependencies. They certify neither aggregate C0012 nor the unproved exhaustiveness implication, and do not cover the subsequently added imprimitivity deduction. No computation or formal verification was used.

The same two reviewers independently accepted the imprimitivity deduction at exact source `4fb53fc81e05a67022f06c947b05f0aae05987af`, conditional on the Bruck structure and fiber inputs with their recorded CFSG/source qualifications, C0011 and the previously reviewed isotope and witness interfaces. They checked exclusion of e=0 and P=1, the strict intermediate subgroup in each route, and preservation of the one-sided permutation action under isotope transport. They did not prove two-family exhaustiveness, primitive-loop nonexistence, or the converse implication. No computation or formal verification was used.

## Symmetric exact factorizations and full inverted folders

**Continuation of 0323:C0010, with the scoped independent reviews below.** Let G be any finite group, τ an automorphism with τ²=1, and H≤G such that

    H∩τ(H)=1,    |G|=|H|².                             (14)

Then K={g∈G:τ(g)=g⁻¹} is inverse- and sandwich-closed and is a transversal to every conjugate of H. Thus it defines a left Bol loop. Under the arbitrary-principal-isotope calculation above, this loop is a G-loop. Core-freeness and generation of G by K are separate conditions; (14) alone does not assert that G is its faithful canonical multiplication group. No odd-order hypothesis is needed for this lemma.

The products G=Hτ(H)=τ(H)H are exact. Write g=h₁τ(h₂). Comparing τ(g)=τ(h₁)h₂ with g⁻¹=τ(h₂⁻¹)h₁⁻¹ in the unique τ(H)H factorization gives h₂=h₁⁻¹. Hence

    K={hτ(h⁻¹):h∈H},   |K|=|H|=[G:H].                 (15)

In the formal semidirect product G⋊⟨t⟩, let Λ=tK. It is the full set of outside involutions. Since C_H(t)≤H∩τ(H)=1, the H-conjugacy orbit of t has size |H|, which is all of Λ by (15). Therefore Λ=t^H is also a G-conjugacy class, even if G has even order.

If x∈H∩Λ², write x=λμ with λ,μ∈Λ. The involution λ inverts x. An H-conjugation sends λ to t while keeping x inside H, so its image x′∈H satisfies τ(x′)=x′⁻¹ and belongs to H∩τ(H)=1. Thus H∩Λ²=1. As K⁻¹=K and Λ²=K² is G-conjugacy invariant, the same collision-free property holds for every conjugate of H. The cardinality (15) gives all the transversals. Full inversion makes K inverse- and sandwich-closed, proving the Bol assertion.

Moreover H is regular on Λ. For each k∈K, choose h∈H sending t to tk. Its conjugation preserves H and sends K=tΛ to (tk)Λ=k⁻¹K. Thus it identifies the loop with every shifted principal-isotope folder; the all-exponent calculation above covers arbitrary loop isotopes. If the presentation is not generated or faithful, perform this calculation in its generated permutation action; conjugation by h preserves that action and the section. No simplicity assumption is used for this deduction.

This criterion concerns a factorization of the envelope G itself, exchanged by τ. It must not be conflated with the earlier intrinsic witness for the specific construction from an exact factorization of another group X. The reviewed cross-coupled examples satisfy (14) but have no such earlier witness. Nor does the lemma assert that every finite simple Bol folder satisfies (14). Its immediate use is to certify higher-class Lie data with complementary stabilizer subalgebras and central graph labels, without a separate search through nonlinear BCH products. At exact source `7fbfbc5a56f4bb1ead9a4d6202c2d948a67950d8`, GPT-6.1 Terra reviewers [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted this subsection, conditional on the previously reviewed general folder and principal-isotope interfaces. Both checked the exact factorization count, full outside orbit in arbitrary parity, marked collision, all-conjugate transversals and reduction of nongenerated or nonfaithful presentations in the isotope argument. No computation, novelty or formal verification is claimed.
