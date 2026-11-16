# Stabilizer alignment through odd normal layers

This is a continuation of 0323:C0010 [context outside this selected packet: `../claims/C0010.md`], specifically 0323.NONBRUCK_ODD. Its bounded obligation is to identify what can prevent the nonconjugate stabilizers H and τ(H) from becoming conjugate when one elementary normal layer is restored. The [nonconjugacy theorem](odd-folder-radicals.md#stabilizer-nonconjugacy-and-exclusion-of-metabelian-envelopes) has scoped independent acceptance at `e896039d004ff3882621aca115b1a39cc8fed207`. The initial dichotomy, nonsimple finite control and later deduction for the simple Q_{p,q} family have the separate scoped reviews below. None proves exact-factorization necessity.

## A first-alignment dichotomy

Let G be a finite odd-order group with an automorphism τ satisfying τ²=1, and let H≤G. Let M<N be τ-stable normal subgroups such that V=N/M is elementary abelian of characteristic p. Write G₀=G/M, H₀=HM/M, A=G/N, J=HN/N≤A, and W=H₀∩V. Assume H₀ and τ(H₀) are not G₀-conjugate, while J and τ(J) are A-conjugate. All involutions below are taken in the formal semidirect product G₀⋊⟨τ̂⟩, even if τ induces identity on a quotient.

Choose θ outside G₀ that normalizes J under the induced action on A. Such a θ exists by the assumed conjugacy of J and τ(J). Conjugation on V factors through A because V is abelian. The subspaces W and W^θ are J-invariant. Exactly one of the following occurs:

1. W and W^θ lie in distinct N_A(J)-orbits. No element outside G₀ can normalize both J and W.
2. Those orbits agree. Then H¹(J,V/W)≠0. Consequently p divides |J| and (V/W)^{O_{p′}(J)}≠0, where O_{p′}(J) is the largest normal subgroup of order prime to p.

To prove the alternatives, every outside element normalizing J differs from θ by an element of the inverse image of N_A(J). Its action on V depends only on its A-image. Thus simultaneous normalization of J and W is equivalent to the stated equality of orbits, independently of the initial choice of θ. In case (2), choose such a simultaneous normalizer θ′. Then H₀ and H₀^{θ′} both lie in H₀V, project onto J, and intersect V in W. The subgroup W is normal in H₀V because H₀ normalizes it and V is abelian. Therefore H₀/W and H₀^{θ′}/W are two complements to V/W in (H₀V)/W. If H¹(J,V/W)=0, their cocycles differ by a coboundary, so the complements are conjugate by V/W. Taking inverse images gives G₀-conjugacy of H₀ and H₀^{θ′}, hence of H₀ and τ(H₀), a contradiction.

For the final consequences, coprime averaging gives H¹(J,E)=0 if p does not divide |J|, for E=V/W. More generally put U=O_{p′}(J). For any 1-cocycle δ:J→E, subtract the coboundary b−j·b, where b=|U|⁻¹∑_{u∈U}δ(u), to arrange δ|_U=0. For u∈U and j∈J, normality gives

    u·δ(j)=δ(uj)=δ(j(j⁻¹uj))=δ(j).

Thus all adjusted values lie in E^U. If E^U=0, every cocycle is a coboundary, contradicting case (2). This is an explicit degree-one argument and uses no spectral-sequence assumption.

For a simple nonassociative odd Bol loop, G is odd and solvable by the FKP/Feit–Thompson inputs recorded in [REFERENCES.md](../REFERENCES.md), and H and τ(H) are nonconjugate by the reviewed theorem above. A chief series for G⋊⟨τ̂⟩ inside G has elementary τ-stable factors. At the bottom the stabilizers are nonconjugate; at the top both images are trivial. Hence an earliest alignment layer exists and satisfies the dichotomy. This supplies an exhaustive split at that layer, not a description of all admissible groups or folders. Neither G₀ nor A is asserted to be the multiplication group of a quotient loop: normal-layer projection of the section is generally not a transversal.

## Simultaneous alignment in the original envelope

In the original faithful simple odd envelope, take a nonzero proper τ-stable elementary normal p-subgroup V≤G, J=HV/V, W=H∩V. If an outside element normalizes J and W, an odd power of it is an involution with the same normalization properties, because G has odd order. The reviewed marked-class identity H∩H^λ=C_H(λ) for all outside involutions then gives W≤C_V(λ). The degree-one obstruction above also applies. This pointwise-fixing conclusion uses the original folder; it is not asserted for arbitrary projected H₀.

If V=G′′ is elementary abelian, the quotient G/V is metabelian, but J is proper: J=G/V would give G=HV and |Q|=[V:W], a prime power, contrary to C0011 [context outside this selected packet: `../claims/C0011.md`], proof §§1–2, scoped review `932ead5db5f39045e2085caa6b062f6b981b2813`. The strict-defect result in [the odd-envelope manuscript](odd-folder-radicals.md) gives |W|<|C_V(τ)|. Thus the projected inverted set has more elements than a transversal to J; the metabelian exclusion for canonical simple envelopes cannot be applied to this quotient.

## A faithful nonsimple control with an irreducible layer

The first branch cannot be removed using only minimality of V, faithfulness, generation and the original Bol transversal property. The following fixed example has those properties and fails simplicity.

Let F=F₃[t]/(t³−t+1) and E=F[i]/(i²+1), with σ(x+iy)=x−iy. The cubic has no root in F₃, so F has 27 elements; −1 is a nonsquare in F, so E has 729 elements. Put ζ=2t²+i(t+t²). Exact arithmetic gives ζ⁷=1, ζ≠1 and σ(ζ)=ζ⁻¹. Let G=E⁺⋊⟨a⟩, where a acts by multiplication by ζ, and set τ(v,a^j)=(σ(v),a^−j). The subgroup V=E⁺ is irreducible as an F₃⟨a⟩-module because ord₇(3)=6, and hence minimal normal in G.

Define the F₃-linear map f:F→F by f(1)=0, f(t)=t+t² and f(t²)=2t², and take

    H=W={x+i f(x): x∈F},     K={g∈G: τ(g)=g⁻¹}.

For ζ^j=a_j+i b_j, where a_j,b_j∈F, the determinant of the F₃-linear map x↦a_j x+b_j f(x) is as follows. Multiplication by a_j and b_j is field multiplication, not multiplication by F₃ scalars.

| j | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| determinant | 1 | 1 | 2 | 2 | 2 | 1 | 2 |

These nonzero determinants say W∩ζ^j iF=0 for every j: ζ^−j(x+i f(x)) has real part a_j x+b_j f(x). Every G-conjugate of H is ζ^rW. The fiber of K above a^j consists of the vectors satisfying v+ζ^jσ(v)=0, namely ζ^{j/2}iF, where j/2 is taken modulo seven. For a fixed H-conjugate and fixed j, a collision in a left coset would give a nonzero vector in the intersection of one such line with a scalar multiple of W, excluded by the determinant table. There are seven fibers of size 27, so |K|=189=[G:H]. Therefore K is a transversal to every conjugate of H. It contains identity, is inverse-closed and closed under xyx, giving a left Bol folder by C0001 [context outside this selected packet: `../claims/C0001.md`].

The core of H in G is zero: it is a G-invariant proper subspace of irreducible V. The section generates G: it contains (0,a) and K∩V=iF; the conjugates of any nonzero vector in iF span irreducible V. Thus this is a faithful generating folder, so its G is canonical.

Both H and τ(H) project to the identity subgroup in G/V=C₇. Nevertheless τ(H) is different from every G-conjugate ζ^jH. For j=0, the graph value at t separates H from σH. For j=1,…,6, ζ^j·1=(a_j,b_j) does not lie in σH, since b_j≠−f(a_j). These explicit inequalities and the determinant table are checked by the standalone certificate below. Consequently no outside element normalizes W. The example realizes case (1) with M=1, N=V and J=1, despite V being irreducible minimal normal.

This loop is non-Bruck because τ(H)≠H, by the [stabilizer test](exact-factorization-criterion.md#bruck-stabilizers-and-necessary-witness-tests), reviewed at `d9bc55095490d42e41c359bbb88b67c78f6d4998`. It is nonsimple: |H∩V|=27=|C_V(τ)|, so the reviewed odd quotient criterion gives a loop homomorphism onto C₇ with kernel K∩V of order 27. It therefore violates the strict-defect condition required of simple loops. It also fails HG′=G: here G′=V and H≤V. Thus this control alone does not decide whether those additional conditions repair alignment. The subsequent source-data deduction addresses simplicity, with a different kind of normal layer.

## The known simple family realizes the orbit obstruction

**Deduction from the C0003 construction, with the scoped review below.** Let p be an odd prime and q a prime divisor of (p^p−1)/(p−1). Use the simple proper odd loop Q_{p,q} in [C0003, proof Theorem 1.1(3)](../proofs/C0003.md), whose historical review is pinned at `9431ade99316d6bc62efb389492fef385b510b45`. We use that source's explicit canonical folder and simplicity assertion as inputs, without a new review of all C0003.

Write F=F_{p^p}, φ(z)=z^p, X=F⁺⋊(C_q⋊⟨φ⟩), and G={(x,y)∈X²:xy∈X′}, with τ interchanging the two coordinates. Set

    M=F⁺×F⁺,  T=C_q×C_q,  t=(φ,φ⁻¹),  N=M⋊T.

The construction gives G/M=T⋊⟨t⟩ and J=HM/M=(1×C_q)⋊⟨t⟩, with H∩M=(ker Tr)×0. Since ord_q(p)=p>1, the eigenvalues p and p⁻¹ of t on T are nontrivial and distinct. Thus [t,T]=T. Each C_q acts irreducibly and without fixed vectors on its field coordinate, so [T,M]=M. Consequently

    G′=N,  G′′=M,  G/N≅C_p,  HG′=G.

The stabilizers H and τ(H) are nonconjugate already because their intersections with M lie nontrivially in different normal coordinate subgroups. In G/M their images J and τ(J) are still nonconjugate: their intersections with T are the distinct axes 1×C_q and C_q×1, each normal in G/M. In G/N, however, both stabilizer images are all of C_p. Thus the first alignment along 1<M<N<G occurs at the elementary q² layer N/M. At that layer, W=J∩T=1×C_q and τ(W)=C_q×1. Every inner element of G/M preserves each axis, while each outside element interchanges them. Hence no outside element normalizes W. This is exactly case (1) of the dichotomy in an actual simple odd folder with HG′=G.

Moreover no choice of an elementary τ-chief series avoids this layer. The action of G on M is faithful modulo M, so C_G(M)=M. Its two coordinate modules are irreducible and nonisomorphic under C_q×C_q, and τ interchanges them. Therefore M is the unique minimal nonzero τ-stable normal subgroup of G: any nontrivial normal subgroup meets M (otherwise it centralizes M and lies in M), and any nonzero τ-stable G-submodule of M contains both coordinates. In G/M, C_{G/M}(T)=T because the C_p action on T is faithful. The distinct eigenaxes and their interchange similarly make T the unique minimal nonzero τ-stable normal subgroup of G/M. The final quotient G/N has prime order. Thus the displayed three-step series is forced.

The strict-defect inequalities in the original simple envelope also hold: for L=M and L=N respectively,

    |C_L(τ)|/|H∩L| = p^p/p^{p−1} = p,
    |C_L(τ)|/|H∩L| = (p^p q)/(p^{p−1}q) = p.

No strict-defect assertion or loop structure is transferred to G/M. In particular, this example does not permit applying the metabelian exclusion to the projected group.

This is an obstruction to eliminating the orbit branch, not a new loop or a counterexample to exact-factorization exhaustiveness: Q_{p,q} already comes from exact factorization. Its critical τ-chief layer splits into two nonisomorphic G/M-modules interchanged by τ. The earlier order-189 control instead has a layer irreducible for G itself and is nonsimple. The revised open target is whether a genuinely G-irreducible, τ-stable first-alignment layer can occur in a simple odd loop, and how the possible paired layers assemble into the intrinsic exact-factorization witness. Neither necessity is proved here.

## Evidence and limits

[verify_odd_stabilizer_alignment.py](../code/verify_odd_stabilizer_alignment.py) is a fixed-input standard-library certificate, with assertions enabled and no search, file output or external dependency. It verifies the field data, seven determinants, all subspace and nonconjugacy statements, the core, all seven conjugate transversals, twisted-subgroup closure, and generation. Root read the complete script and ran it with Python 3.12.14, reproducing G=5103, H=27, K=189 and quotient/kernel orders 7/27. The proof of the general dichotomy and the later simple-family deduction are separate from this finite arithmetic; neither the computation nor the dichotomy proves classification exhaustiveness.

GPT-6.1 Terra reviewers [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the initial dichotomy, original-envelope refinements and order-189 nonsimple control at exact source `644f87c3d6aa33bcd419074bd7ef6da95bb8f1ba`, conditional on the cited folder and odd-envelope inputs. Both inspected the entire pinned certificate and ran it independently with Python 3.12.14, reproducing all assertions and stated sizes. They retained the control's failure of both strict defect and HG′=G and did not infer a simple-loop example from it. These reviews do not cover the subsequently added Q_{p,q} first-alignment deduction.

The same two reviewers separately accepted the Q_{p,q} deduction at exact source `9d806247691956ef2dfb7a39ff32fe2934fde351`, conditional on the cited explicit C0003 folder and simplicity inputs and the earlier dichotomy. They checked the derived groups, stabilizer images, self-centralizers and forced τ-chief series, the unaligned first layer and both strict-defect ratios. They retained the distinction between a paired layer irreducible for the τ-extension and a layer irreducible for G itself. No new computation was used for this deduction, and neither review reaudited all of C0003 or proved exact-factorization necessity. No formal verification is claimed.
