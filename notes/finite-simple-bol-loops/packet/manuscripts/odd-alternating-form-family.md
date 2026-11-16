# Simple odd Bol loops from alternating-form tuples

**Continuation of 0323:C0010 [context outside this selected packet: `../claims/C0010.md`], with exact-source reviews below.** The construction below gives a family of finite simple proper odd Bol G-loops and an exact isomorphism relation within the family. It uses the class-two normal-form and isomorphism criterion at source `226a8dc1eb503026c350ffe3b7ac93da9077a593`, the symmetric factorization lemma at `7fbfbc5a56f4bb1ead9a4d6202c2d948a67950d8`, and the strict-defect and properness interfaces used in the construction reviewed at `722ba8c289c96dfd87c98f9a5ab3dcb8b2080998`. The present theorem has the separate independent reviews recorded below. It does not classify all simple Bol loops or assert a matrix-pair embedding or a complexity result.

## The theorem

Let p and q be distinct odd primes with p dividing q−1, put r=ord_q(p), E=F_(p^r), and fix positive integers n,k. Choose λ∈E of order q and η∈Fq of order p. Let B=(B₁,…,Bₖ) be alternating n×n matrices over E, linearly independent over Fp and with zero common radical. Then the construction below gives a simple proper Bol G-loop of order

    p^(nr+k) q^(2k+1).                                      (1)

For fixed p,q,n,k and the fixed choices of λ and η, two such inputs B and B′ give isomorphic loops if and only if there are a permutation π∈Sₖ, a field automorphism θ∈Gal(E/Fp), and L∈GL_n(E) such that

    Lᵀ B′_{π(i)} L = θ(Bᵢ)     for i=1,…,k.                 (2)

In (2), θ is applied entrywise. The tuple need only be Fp-independent; E-linear independence is not assumed.

## Construction

Write Z=Fp^k and W=E^n, and define the alternating map

    β(x,y) = (Tr_(E/Fp)(xᵀBᵢy))ᵢ ∈ Z.

Nondegeneracy of the field trace shows that β has zero radical and spans Z, by the stated hypotheses. Form the exponent-p class-two group P on W⊕W⊕Z with BCH product and bracket

    Ω((x,y),(x′,y′)) = β(x,y′)+β(y,x′).

Thus Z(P)=P′=Z. Let V=⊕_(i=1)^k Fq² with γ the sum of the standard alternating forms on its planes. Define the exponent-q extraspecial group Q on V⊕V⊕Fq by the analogous BCH construction using γ.

Let A=A_p×A_q, where A_p=Fp^k additively and A_q=<c> has order q. The element a=(aᵢ)∈A_p acts trivially on P and on the ith plane of the two halves of Q by η^(aᵢ) and η^(−aᵢ), respectively. The element c acts on the two W halves of P by λ and λ^−1 and trivially on its center and on Q. These actions preserve the brackets. Let G=(P×Q)⋊A, and let τ swap each pair of halves, fix both centers and invert A. Put

    H=(W×V) ⋊ { (a, t; a, c^t) : a∈Fp^k, t∈Fq },       (3)

where the first a,t in the displayed graph lie in Z(P), Z(Q), and the second a,c^t lie in A. Set K={g∈G:τ(g)=g^−1}.

The cross actions give G′=P×Q: c−1 is invertible on P/Z, and the A_p action has no common fixed vector on Q/Z; the brackets span the centers. The A action on P×Q is faithful. Moreover H∩τH=1, since the first axes meet the swapped axes trivially, the graph is injective, and A has odd order. Direct counting gives |H|²=|G|. The symmetric factorization lemma at `7fbfbc5a56f4bb1ead9a4d6202c2d948a67950d8` therefore gives a full inverted-set Bol folder and the G-loop property. Its core is trivial: a normal subgroup in H has trivial image in A because its commutators with P×Q lie in the first axes whereas the cross actions are faithful, and then trivial intersection with P×Q because a normal subgroup in an isotropic first axis centralizes P×Q only when its vector is zero. Also <K>=G by the generating-folder interface, using G′=P×Q and the projected inverted torus. The index [G:H] is (1).

## Simplicity

Use the strict-defect criterion from the stated reviewed interfaces. Let N be τ-stable and normal in G. Put Lp=N∩P, Lq=N∩Q, Cp=Lp∩Z(P), and let Tp,Tq be the p- and q-primary parts of the image of N in A. Likewise let Jp,Jq be the corresponding images of H∩N. These definitions include nonsplit lifts; no quotient-transversal assertion is used.

Coprime averaging by A_q separates Cp from the vector part of Lp, because A_q has no nonzero fixed vector on P/Z(P). The first-half injection into the τ-positive part gives

    |C_Lp(τ)| / |H∩Lp| ≥ |Cp|.                             (4)

If h∈H∩N has p-torus label a, take its p-part and commute it with c. Since λ−1 is invertible, these commutators extract the first-half P component into N. After removing it, the P-center component of hτ(h) is 2a. Hence a∈Cp and |Jp|≤|Cp|. Similarly |Jq|≤q. If Lq is nontrivial, normality and nondegeneracy of Q force it to meet Z(Q); its τ-fixed center and the first-half injection give

    |C_Lq(τ)| / |H∩Lq| ≥ q.                               (5)

If Jq is nontrivial and Lq=1, choose a q-element of H∩N with nonzero A_q label. Its Q first-axis component must centralize Q by normality, because A_q acts trivially on Q, so that component vanishes. Its product with its τ-image then has nonzero Q-central component, a contradiction. Thus Jq can cancel (5) only when Lq is nontrivial.

If Tq≠1, a lift acts fixed-point-freely on P/Z(P), so normality forces Lp=P. If Tp is proper, the p contribution is strict: |Jp|≤|Tp|<|Z(P)|. If Tp=A_p as well, commutators with the coordinate characters force Lq=Q, so N=G. If Tq=1 and Tp≠1, at least one Q character is moved, so Lq is nontrivial while Jq=1, and the q contribution is strict. Finally, if Tp=Tq=1 and N≠1, at least one nontrivial Lp or Lq has nonzero central intersection, giving strict defect. Thus every proper nontrivial τ-normal subgroup has strict defect, and the cited criterion gives simplicity.

## Properness

Fix i and restrict to A_p=<eᵢ>, the corresponding line of Z(P), the ith plane Fq² of V and Z(Q). The loop operation on this subloop, in coordinates (u,t,s)∈Fq²×Fp×Fq, is

    (u,t,s)·(v,r,h)=(u+η^t v,t+r,s+h−γ(u,v)).            (6)

This follows directly from the transversal calculation in the cited `722ba8c289c96dfd87c98f9a5ab3dcb8b2080998` construction. Choose v,w with γ(v,w)=1 and put X=(0,1,0), Y=(v,0,0), Z₀=(w,0,0). In the Moufang identity (XY)(Z₀X)=(X(YZ₀))X, the two sides have equal noncentral coordinates and central coordinates −η and −1, respectively. Since η≠1, the loop is not Moufang.

## Isomorphisms within the family

Apply the complete isomorphism criterion (15) of the reviewed class-two normal form at `226a8dc1eb503026c350ffe3b7ac93da9077a593`. A folder isomorphism preserves each prime factor and its first axis. The Q first axis has exactly the k distinct characters a↦η^(aᵢ). Since η lies in the prime field Fq, intertwining these characters forces the induced automorphism of A_p to be a coordinate permutation: write E_Ap(eᵢ)=e_{π(i)}. The P central graph forces the same permutation on Z.

On W, intertwining c with its image c^u forces u≡p^j (mod q) for some j and the axis map to be L∘θ, where θ(x)=x^(p^j) on E and L∈GL_n(E). Nondegeneracy and Frobenius invariance of the trace then give exactly (2).

Conversely, given π, θ and L satisfying (2), use L∘θ on the P first axis and its τ-corresponding map on the second, with the center map eᵢ↦e_{π(i)}. Send c to c^u, where u≡p^j (mod q) represents θ. On the Q first axis permute the character planes by π and choose an alternating similitude of multiplier u on each two-dimensional Fq plane; use the corresponding map on the second axis and multiplication by u on Z(Q). These maps intertwine the actions and preserve the two central graphs. Criterion (15) therefore gives a folder, hence loop, isomorphism. This proves (2), conditional on the cited criterion.

At exact source `2a25b81e3efe5bdd8a3923e27c94aef16a559094`, GPT-6.1 Terra reviewers [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the entire theorem under its pinned class-two strict-isomorphism, symmetric-factorization, strict-defect and restricted-section inputs. Both checked trace-form spanning and radical conditions over Fp, canonical generation/core-freeness, every τ-normal strict-defect case including nonsplit lifts, the actual subloop Moufang witness, the forced coordinate permutation and Frobenius exponent, the exact orientation of (2), and the converse using q-side similitudes. No computation or fresh primary-source audit was performed; these reviews cover this fixed-parameter family, not a general census or complexity claim.
