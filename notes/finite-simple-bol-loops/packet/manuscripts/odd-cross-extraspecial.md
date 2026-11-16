# A cross-coupled extraspecial candidate outside the exact-factorization route

**Result with the scoped independent reviews below.** This is a continuation of 0323:C0010 [context outside this selected packet: `../claims/C0010.md`] and 0323.NONBRUCK_ODD, with no new permanent claim ID. The bounded obligation is to test whether every simple nonassociative odd Bol folder has a minimal normal subgroup exchanged with a distinct subgroup by its canonical inversion. Such a pair is necessary for the intrinsic exact-factorization witness: a nontrivial normal N disjoint from τ(N) contains a minimal normal M with M≠τ(M), and conversely distinct minimal normals have trivial intersection.

The construction below gives a finite simple proper left Bol loop of order 3⁷·13³=4,804,839 with canonical LMlt center C₃×C₁₃ and exactly those two central factors as its minimal normal subgroups. Both are fixed pointwise by τ. Under the cited interfaces, this refutes both the paired-minimal necessity and exact-factorization exhaustiveness, and realizes nilpotent derived subgroup with extraspecial Sylow factors. The loop lies outside the Bruck-isotopy route by the reviewed odd-envelope nonconjugacy theorem. This is a counterexample to a workspace conjecture, not a complete classification or a claim of literature novelty; novelty has not been audited.

The interfaces are the faithful-folder correspondence in C0001 [context outside this selected packet: `../claims/C0001.md`], canonical inversion in C0007 [context outside this selected packet: `../claims/C0007.md`], the [odd strict-defect simplicity criterion](odd-folder-radicals.md#candidate-simplicity-criterion-using-τ-stable-normal-subgroups) independently reviewed at `65a3e58df517df59656ab948ac9d122208f62c4a`, and the [intrinsic witness](exact-factorization-criterion.md). The proof gives the full section, transversality, faithfulness, generation and normal-subgroup calculation explicitly. It uses neither an enumerated multiplication table nor an assumption that arbitrary normal-subgroup projections are folders.

## Construction

Let p=3,q=13. Put E=F_{27}, F=F_{13}, W_p=E², W_q=F². For r=p,q, write P_r=(W_r⊕W_r^*)×F_r with Heisenberg product
 (x,y,z)(x',y',z')=(x+x',y+y',z+z'+½ Tr(x·y'−y·x')),
where the trace is E→F3 on the p-side and identity F13→F13 on the q-side. Then |P_p|=p^13, |P_q|=q^5, and their centers Z_p,Z_q have orders p,q. Let a_q of order q act on P_p by diag(ζ,ζ^−1), with ζ of order 13 in E; let a_p of order p act on P_q by diag(η,η^−1), with η of order 3 in F. Each fixes the center; the other actions are trivial. Set G=(P_p×P_q)⋊(⟨a_p⟩×⟨a_q⟩), equivalently the direct product (P_p⋊⟨a_q⟩)×(P_q⋊⟨a_p⟩). The two factor orders are not relatively prime.

Let J=[[0,1],[-1,0]] over the appropriate field, and σ_r(x,y,z)=(Jy,J^−1x,z). Direct matrix calculation shows σ_r²=1, preserves the alternating trace pairing, and conjugates each corresponding scalar action to its inverse. Define τ=(σ_p,σ_q) and τ(a_p)=a_p^−1, τ(a_q)=a_q^−1. Put S_r={(x,0,0):x∈W_r}, choose nonzero central generators z_p,z_q, and define
 H=(S_p×S_q)⋊⟨a_p z_p, a_q z_q⟩.
This is a subgroup: the twisted generators commute, have orders p,q, and normalize the S_r. The fixed subgroups C_{P_r}(τ) have size |W_r|·r, while τ inverts both odd cyclic A-factors. Thus |C_G(τ)|=(p^6 p)(q² q)=|H|, and K={g:τ(g)=g^−1} has |K|=[G:H] by coprime complement conjugacy. Its size is p^7 q³=4,804,839.

## Transversality without enumerating the loop

For a single factor T=P_r⋊⟨a_s⟩ with r≠s, cross scalar ξ≠1, σ swapping W and W*, and center fixed by τ, consider x=(w,0,z)a_s^j with w∈W. Then x is inverted by some τ-conjugate involution iff either j≠0 and z=0, or j=0 and w=z=0.

If j≠0, 1−ξ^j is invertible on W, so conjugating by a W-translation kills w without changing z (W is isotropic). Thus x is conjugate to z a_s^j. If an outside involution inverted z a_s^j, then it would send a_s^j to z^−2 a_s^−j, because it fixes the central z. The target has order rs when z≠0, but automorphisms preserve the order s of a_s^j, contradiction. If z=0, the pure a_s^j is inverted by τ, and conjugacy supplies an involution inverting x.

If j=0, conjugation by P_r acts trivially on P_r/Z_r, while conjugation by powers of a_s preserves W and W*. Every conjugate of σ swaps these complementary subspaces, so it cannot send a nonzero w∈W to −w. If w=0 and z≠0, the central element z is fixed by every τ-conjugate and cannot be inverted in odd order. This proves the criterion.

Now write an arbitrary h∈H using labels i mod p, j mod q. Its p-coordinate is (w_p,0,i z_p)a_q^j, and its q-coordinate is (w_q,0,j z_q)a_p^i. (The additive central coefficients are i and j in their respective prime fields.) In G⋊⟨τ⟩, τ-conjugate involutions act independently on the two direct factors. If i,j are both nonzero, the first criterion fails because j≠0 but i z_p≠0. If i≠0,j=0, its p-coordinate has label 0 and nonzero central part; the case i=0,j≠0 is symmetric. If both labels are zero, any nonzero w_r fails the label-zero criterion. Therefore no nonidentity h∈H is inverted by any τ-conjugate involution.

Because |G| is odd, all involutions in τG form the single class Λ=τ^G. An element is in Λ² iff it is inverted by some λ∈Λ: if h=λλ′ then λhλ=h^−1; conversely λ and λh are involutions in τG. Thus H∩K²=H∩Λ²=1. Λ² is G-conjugacy invariant, so K has no collisions in any conjugate H-coset, and the size equality makes it a transversal. It contains 1, is inverse-closed and xyx-closed by τ-inversion. Hence (G,H,K) is a left Bol folder under C0001 Theorem 1.3.

## Faithfulness and generation

The core of H is trivial. Indeed, if N◁G lies in H then N∩(P_p×P_q) is a normal subgroup of the direct product contained in S_p×S_q. Any nontrivial normal subgroup of either extraspecial factor meets its center, but S_r∩Z_r=1, so this intersection is 1. Consequently N centralizes P_p×P_q; the cross scalar actions are faithful and each extraspecial centralizer in itself is its center, so C_G(P_p×P_q)=Z_p×Z_q. The latter intersects H trivially, giving N=1.

The two cross scalar actions have no nonzero fixed vectors on the appropriate symplectic spaces, so commutators with a_q and a_p generate P_p and P_q respectively, including their centers. Hence G′=P_p×P_q and G/G′=C_p×C_q. τ inverts the latter. The subgroup generated by K is normal: every τ-inverted element is g^−1τ(g) (take g=k^−1/2 in odd G), and the subgroup generated by τ-commutators is normal. On the quotient by that subgroup τ is trivial, while its action on the quotient abelianization is inversion. A nontrivial odd solvable quotient has nontrivial abelianization, so the quotient is trivial. Thus K generates G.

## Normal-subgroup calculation

The key module fact is that \(W_p\) and \(W_p^*\) have distinct irreducible constituents under the cross scalar. For \(p=3\), \(\operatorname{ord}_{13}(3)=3\), an odd number, so inversion is not a Frobenius power; for \(p=13\), the two distinct one-dimensional characters are \(\omega_3\) and \(\omega_3^{-1}\). Semisimplicity gives, for every \(\tau\)-stable \(a_q\)-submodule \(U\le W_p\oplus W_p^*\), a unique form
\[U=U_0\oplus\tau(U_0),\qquad U_0=U\cap W_p.\tag{1}\]
The multiplicity of each irreducible is two, and (1) is valid for arbitrary multiplicity subspaces, not only coordinate lines. The \(\tau\)-fixed space in \(U\) is its graph, of dimension \(\dim U_0\).

Let \(L\triangleleft G\) be a nontrivial \(\tau\)-stable subgroup contained in \(P_p\). If \(L\not\le Z_p\), normality under \(P_p\) gives \(Z_p\le L\): a noncentral element has a nontrivial commutator with \(P_p\), and \(|Z_p|=p\). The center-only case also has \(Z_p\le L\). Thus \(Z_p\le L\), and \(L/Z_p=U\) satisfies (1). Since \(\tau\) fixes \(Z_p\) and has order two coprime to \(p\), fixed-point lifting gives
\[|C_L(\tau)|=p^{1+\dim U_0}=p\,|L\cap S_p|.\tag{2}\]
The last equality follows because \(L\) contains the full center and the canonical lift of every vector of \(U_0\) in \(S_p\). For \(L=1\), both sides before the factor \(p\) equal 1.

## Normal subgroups inside the extraspecial kernel

Put \(D=P_3\times P_{13}\). If \(N\triangleleft G\) lies in \(D\), its Sylow factors are \(L_3=N\cap P_3\) and \(L_{13}=N\cap P_{13}\), and \(N=L_3\times L_{13}\). If \(N\) is \(\tau\)-stable, so are its factors. By (2),
\[\frac{|C_N(\tau)|}{|H\cap N|}=\prod_{p:L_p\ne1}p>1\quad(N\ne1).\tag{3}\]
This covers central and noncentral factors, including arbitrary invariant multiplicity subspaces.

## A single torus coordinate in the image

The image of any normal subgroup in \(A\cong C_3\times C_{13}\) is one of \(1,\langle a_3\rangle,\langle a_{13}\rangle,A\). Suppose \(\pi(N)=\langle a_p\rangle\), and write \(q\ne p\). The commutator of a lift of \(a_p\) with \(P_q\) has full image on \(P_q/Z_q\), because its two scalar eigenvalues differ from 1; it therefore generates all of \(P_q\), including its center. Normality gives \(P_q\le N\). Since \(P_q\) is contained, one may cancel the \(P_q\)-coordinate of each element, obtaining the internal semidirect-product decomposition
\[N=P_q\rtimes N_p,\qquad N_p=N\cap(P_p\times\langle a_p\rangle).\tag{4}\]
The \(a_p\)-coordinate acts nontrivially on \(P_q\), so this is generally not a direct product. Both \(P_q\) and \(N_p\) are \(\tau\)-stable.

Let \(L=N_p\cap P_p\). If \(Z_p\not\le L\), normality under \(P_p\) forces \(L=1\), and any lift of \(a_p\) in \(N_p\) has central \(P_p\)-coordinate \(z_p^j\). The \(\tau\)-stability of \(\langle a_p z_p^j\rangle\) forces \(j=0\), because \(\tau(a_pz_p^j)(a_pz_p^j)=z_p^{2j}\) and \(p\) is odd. Thus \(N_p=\langle a_p\rangle\), \(C_{N_p}(\tau)=1\), and \(H\cap N_p=1\).

If \(Z_p\le L\), write a lift as \(a_pu\) with \(u\in P_p\). Normality under \(a_q\) implies \((a_q-1)(uZ_p)\in L/Z_p\); the cross scalar has no eigenvalue 1, so it follows that \(uZ_p\in L/Z_p\), whence \(u\in L\). Therefore \(a_p\in N_p\) and
\[N_p=L\times\langle a_p\rangle,\qquad |C_{N_p}(\tau)|=|C_L(\tau)|.\tag{5}\]
The actual stabilizer contributes \(p|S_p\cap L|\): because \(z_p\in L\), the element \(a_pz_p\) lies in \(N\), while no nonidentity \(a_q\)-coordinate does. Thus (2) gives equality between this local contribution and \(|C_{N_p}(\tau)|\). In the \(Z_p\not\le L\) case both are 1. The full opposite factor \(P_q\) contributes a strict factor \(q\), so
\[|C_N(\tau)|=q\,|H\cap N|.\tag{6}\]
For the fixed subgroup count in the semidirect product, \(\tau\) inverts \(a_p\); its fixed elements have trivial \(a_p\)-coordinate, so (6) is a direct count, not a false assertion that (4) is a direct product.

## Full torus image

If \(\pi(N)=A\), commutators with \(P_3\) and \(P_{13}\) force both into \(N\). Then \(D\le N\) and \(\pi(N)=A\), so \(N=G\). Hence every nontrivial proper \(\tau\)-stable normal subgroup satisfies the strict defect \(|H\cap N|<|C_N(\tau)|\), subject to the group construction and calculations above.

## Simplicity, properness and the failed witness

All hypotheses of the cited strict-defect criterion are now supplied by the folder construction. Equations (3) and (6), together with the full-image case, give strict defect for every nontrivial proper τ-stable normal N. Hence the loop is simple. The criterion uses a maximal proper normal subloop if one exists, so that its quotient is simple and has an inverting translation-group automorphism; it does not presume this for an arbitrary quotient. Its exact dependency and source qualifications remain as recorded at `65a3e58df517df59656ab948ac9d122208f62c4a`.

The loop is nonassociative: a group loop has regular left multiplication group and trivial identity stabilizer, whereas the faithful generating folder here has H≠1. It is non-Moufang using the finite simple Moufang baseline, with its CFSG qualification: Nagy–Vojtěchovský, *Octonions, simple Moufang loops and triality*, arXiv:math/0701707v1, §4.1 Theorem 4.1 and §6.3 Theorem 6.7/Corollary 6.8, as pinned in [REFERENCES.md](../REFERENCES.md). All finite nonassociative simple Moufang loops are Paige loops of even order, while this order is odd. No explicit Moufang-identity witness is supplied by this proof.

The center of G is exactly Z₃×Z₁₃. A central element has trivial torus image because each torus acts faithfully on the opposite extraspecial shadow; within D the center is exactly that product. Every nontrivial normal subgroup inside D contains one of these centers, while any normal subgroup with nontrivial torus image contains an opposite extraspecial group and hence its center. Thus Z₃ and Z₁₃ are the only minimal normal subgroups, both fixed pointwise by τ. If 1≠N◁G, choose one of these minimal normals M≤N. Then M=τ(M)≤N∩τ(N). Consequently there is no nontrivial τ-disjoint normal subgroup, and in particular no intrinsic exact-factorization witness. The separately reviewed odd-center obstruction gives the same conclusion.

The reviewed odd-envelope nonconjugacy result at `e896039d004ff3882621aca115b1a39cc8fed207`, followed by the Bruck-isotopy equivalence at `ea836a5f328d6bc52913aac8fd1841a87072f5f8`, places this simple odd loop outside the Bruck-isotopic class as well. The construction and simplicity argument have the scoped acceptances below. They refute the proposed two-construction exhaustive map and require a broader description; they do not complete the classification.

## Coordinate formula and explicit Moufang failure

**Deduction with the scoped independent reviews below.** Fix η=3∈F₁₃ and keep ζ∈E=F₂₇ of order 13. Identify the cosets G/H with tuples (u,a;v,b), where u∈E², a∈F₃, v∈F₁₃² and b∈F₁₃. A coset has the unique representative ((0,u,a),(0,v,b)) in D after canceling the torus with H and then removing the first coordinates with S₃×S₁₃. The multiplication is

    (u,a;v,b)·(u′,a′;v′,b′)
      = (u+ζ^b u′, a+a′+Tr_{E/F₃}(uᵀJ u′);
         v+3^a v′, b+b′+vᵀJ v′).                  (7)

The exponents are interpreted modulo 13 and 3 respectively. To verify (7), right multiplication of a Heisenberg element (x,y,z) by (−x,0,0) gives (0,y,z+½Tr(yᵀx)), with identity trace on the F₁₃ side. The unique K representative of (u,a;v,b) has torus exponents (i,j)=(−a,−b), first coordinates −ζ^jJu and −3^iJv, and both central coordinates zero. In the product of two K representatives, put c=ζ^{−(b+b′)} and Ω=uᵀJu′. Its E-side second coordinate is u+ζ^b u′, first coordinate −ζ^−bJu−cJu′, and central coordinate ½Tr((1+c)Ω). Canceling the torus on the right adds a+a′ to this central coordinate; removing the first coordinate then adds ½Tr((1−c)Ω). The result is a+a′+Tr(Ω). The F₁₃-side calculation is identical and proves (7).

For e₁=(1,0), e₂=(0,1) over F₁₃, take

    x=(0,1;0,0),    y=(0,0;e₁,0),    z=(0,0;e₂,0).

Direct substitution gives

    (xy)(zx) = (0,2;3(e₁+e₂),3),
    (x(yz))x = (0,2;3(e₁+e₂),1).

Thus the defining Moufang identity in PROBLEM.md fails. This supplies a direct properness proof without using the CFSG-qualified Moufang classification in the earlier reviewed source, conditional on the coordinate identification just proved. The coordinate addition has its own review status below.

## Isotopy scope: this example is a G-loop

**Deduction with the scoped independent reviews below.** This example remains isomorphic to each of its loop isotopes. Indeed H∩C_G(τ)=1: fixedness forces both odd torus labels to vanish, after which the symplectic swaps fix no nonzero element of S₃×S₁₃. Since |H|=|Λ|, H acts regularly on Λ=τ̂^G by conjugacy. For each k∈K choose h∈H with hτ̂h⁻¹=τ̂k. Conjugacy invariance of Λ then gives

    hKh⁻¹=(τ̂k)Λ=k⁻¹K.

Conjugation by h preserves H, so it identifies the original folder with every shifted folder (G,H,k⁻¹K). The arbitrary-principal-isotope calculation in [the reviewed isotope criterion](exact-factorization-criterion.md#bruck-isotopy-as-a-stabilizer-conjugacy-test), reviewed at `ea836a5f328d6bc52913aac8fd1841a87072f5f8`, covers every loop isotope. Consequently this is a G-loop. Being outside the exact-factorization construction does not mean being outside the G-loop class. In particular this example does not solve Nagy's historical question about simple Bol loops that are neither G-loops nor Bruck isotopes. No literature-novelty assertion follows.

## Uniform family for every pair of odd primes

**Extension with the scoped independent reviews below.** Let p<q be distinct odd primes, r=ord_q(p), s=ord_p(q), and m,n positive integers. Put E=F_{p^r}, F=F_{q^s}, W_p=E^{2m}, W_q=F^{2n}, and choose scalars ζ∈E and η∈F of orders q and p. Use standard alternating matrices J_p,J_q of sizes 2m,2n. The cross-coupled construction gives a simple proper left Bol G-loop of order

    p^{2mr+1} q^{2ns+1}.                            (8)

Its canonical left multiplication group has nilpotent derived subgroup P_p×P_q, with extraspecial factors of orders p^{4mr+1}, q^{4ns+1}, and center C_p×C_q. The latter two factors are its only minimal normal subgroups, both fixed by τ. Thus every member has no intrinsic exact-factorization witness and lies outside the Bruck-isotopic route. The construction choices below give one isomorphism class for each tuple (p<q,m,n), and different such tuples give nonisomorphic loops within this family. No assertion of exhaustiveness among all simple Bol loops, all nilpotent-derived envelopes or all loops of these orders is made.

Use the preceding trace-Heisenberg definition on W_p⊕W_p* and W_q⊕W_q*, now taking traces to F_p and F_q. Let a_q act by (ζ,ζ⁻¹) on P_p and a_p by (η,η⁻¹) on P_q, with own-prime and central actions trivial. Set G=(P_p×P_q)⋊(C_p×C_q), define τ by (x,y,z)↦(J_i y,J_i⁻¹x,z) and a_i↦a_i⁻¹, and let

    H=(S_p×S_q)⋊⟨a_p z_p,a_q z_q⟩,
    K={g∈G : τ(g)=g⁻¹}.

Here S_i is the first-coordinate additive subgroup and z_i is the unit generator of the prime-field center. The matrix verification, twisted-generator subgroup calculation and local inversion criterion above use only odd distinct primes, a nontrivial prime-order scalar and an isotropic coordinate subspace. They therefore apply verbatim in these dimensions. In particular |H|=|C_G(τ)|=p^{2mr+1}q^{2ns+1}, the same four torus-label cases give H∩Λ²=1, and hence K is a transversal to every conjugate of H. The core-freeness proof again reduces to the prime-order extraspecial centers, while A⊂K and [P_p,a_q]=P_p, [P_q,a_p]=P_q give generation. This establishes the faithful generating Bol folder uniformly, including even r or s.

### Simplicity without reciprocal-character restrictions

The finite example used inequivalent reciprocal constituents. The uniform proof does not need that condition. Let 1≠L◁G be τ-stable with L≤P_ℓ, where ℓ is p or q. Normality under the extraspecial P_ℓ forces its prime-order center Z_ℓ into L. Put V=L/Z_ℓ and

    a=dim_Fℓ V₊,    w=dim_Fℓ(V∩W_ℓ).

Since τ interchanges the complementary coordinate halves, (V∩W_ℓ)∩V₋=0. Projection along V₋ is injective on V∩W_ℓ, so w≤a. Coprime fixed-point lifting and the full central fiber give

    |C_L(τ)| / |L∩S_ℓ| = ℓ^{1+a−w} ≥ ℓ.           (9)

This remains valid for self-dual scalar modules and diagonal mixed submodules. For L=1 the ratio is one.

Now let N◁G be τ-stable. If N≤D=P_p×P_q, its Sylow factors split and (9) gives strict defect whenever N≠1. If its image in A=C_p×C_q is all A, commutators with both extraspecial groups force N=G. Suppose instead that its image is ⟨a_ℓ⟩. As before, N contains the opposite full extraspecial group P_{ℓ′}, and

    N=P_{ℓ′}⋊N_ℓ,
    N_ℓ=N∩(P_ℓ×⟨a_ℓ⟩),    L=N_ℓ∩P_ℓ.

If Z_ℓ is not contained in L, normality forces L=1 and a lift of a_ℓ to have central coordinate. τ-stability then forces that coordinate zero, so N_ℓ=⟨a_ℓ⟩. Its fixed and actual H-intersection contributions are both one. Otherwise Z_ℓ≤L; invariance under the opposite scalar and invertibility of that scalar minus one on the invariant quotient imply that the P_ℓ component of an a_ℓ lift belongs to L. Thus N_ℓ=L×⟨a_ℓ⟩. The local H contribution is ℓ|S_ℓ∩L| and the fixed contribution is |C_L(τ)|, with ratio ℓ^{a−w}≥1 by (9). The opposite full factor contributes the strict ratio ℓ′. Fixed elements of the semidirect product have trivial a_ℓ coordinate, since τ inverts it; no direct-product fixed-point formula is assumed. These cases prove strict defect for every proper nontrivial τ-stable normal subgroup. The already reviewed maximal-simple-quotient criterion therefore gives simplicity for all parameters.

The center and minimal-normal arguments are unchanged: Z(G)=Z_p×Z_q, and every nontrivial normal subgroup contains at least one of Z_p,Z_q. Hence there is no nontrivial τ-disjoint normal subgroup. The odd nonconjugacy and isotope criterion exclude Bruck isotopy. The H-regularity proof on Λ also remains unchanged because H∩C_G(τ)=1 and |H|=|Λ|; every member is a G-loop.

### Coordinates, properness and parameter identification

The same coset calculation yields

    (u,a;v,b)·(u′,a′;v′,b′)
      = (u+ζ^b u′, a+a′+Tr_{E/F_p}(uᵀJ_pu′);
         v+η^a v′, b+b′+Tr_{F/F_q}(vᵀJ_qv′)).    (10)

Choose c∈F with Tr((η−1)c)≠0, possible because the finite-field trace pairing is nondegenerate and η≠1. With x=(0,1;0,0), y=(0,0;e₁,0), z=(0,0;c e_{n+1},0), the two Moufang products have all coordinates equal except the last, which is Tr(ηc) for (xy)(zx) and Tr(c) for (x(yz))x. Thus every member is proper, without the simple Moufang classification.

Finite-field choices up to isomorphism preserve trace. To see that primitive scalar choices do not create further parameters, replace ζ by ζ^u and η by η^v, with u∈F_q× and v∈F_p×. In the common ambient group the new torus generators are a_q^u,a_p^v. On a local Heisenberg pair, use matrices T=diag(I,λI), T*=diag(λI,I) on the first and second coordinate halves, and scale the center by λ. Their pairing multiplier is λ, they commute with the symplectic swap and with scalar actions, and preserve S_i. For the p-factor take λ=v⁻¹∈F_p×; for the q-factor take λ=u⁻¹∈F_q×. The induced automorphism fixes the torus, commutes with τ, and carries H to the subgroup generated using the new torus generators, after taking the corresponding inverse powers. It therefore gives an isomorphism of faithful folders. A change of nondegenerate alternating matrix J to T J Tᵀ is handled by diag(T,T⁻ᵀ) on the Heisenberg pair, which preserves its pairing and intertwines the swaps.

Exchanging p,q and m,n simply exchanges the two factors. Once p<q is imposed, the prime factorization of (8) recovers p,q and then m,n because r,s are determined by them. Different allowed tuples therefore have different orders and cannot be isomorphic. These are a complete parameter identification and separation for this construction, not a census of arbitrary loops at those orders. The two-prime uniform extension has the scoped independent reviews below; no general computational certificate is claimed.

## Evidence and independent review

At exact source `62978672415973eb0f8043c6976d06b317a52d42`, GPT-6.1 Terra reviewers [model reviewer identity omitted], [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the full construction, transversality, faithfulness, generation, strict-defect simplicity and center/minimal-normal deductions. All checked the cross-character decomposition with arbitrary multiplicity subspaces and both single-torus-image cases, and separately inspected the maximal-simple-quotient proof of the invoked strict-defect criterion. Their acceptances retain C0001/C0007's precisely used interfaces, the reviewed isotope and intrinsic-witness results, and the CFSG-qualified Moufang baseline used in that source. They did not perform formal verification or a literature-novelty audit. Their reviews do not cover the later coordinate formula, direct Moufang witness or G-loop paragraph above.

The standalone [coordinate certificate](../code/verify_odd_cross_extraspecial.py) uses F₂₇=F₃[t]/(t³−t+1), the first encoding of an order-13 element, and η=3. It supplies the finite coordinate operations, compares them with independently implemented Heisenberg semidirect products and coset reduction on fixed-seed samples, and evaluates the displayed Moufang witness. It enumerates neither the whole loop nor all normal subgroups. Sampled Bol identities and the integrity check do not prove universal Bol or simplicity; those assertions rest on the algebraic proof. Root read the complete script before running it. Two independent proof/code reviews of the exact coordinate source are recorded below.

At exact source `55720403eb03a5aad1e4c6c55769a972ffe69e52`, [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the coordinate formula, explicit Moufang failure and G-loop deduction, conditional on the earlier construction and reviewed isotope interface. Both audited the full certificate before independently running its pinned source with bundled Python 3.12.14, reproducing the 104 section/identity/inverse controls, 500 group-coset/Bol samples and witness coordinates 3 versus 1. The direct identity failure removes the need for the finite simple Moufang classification in the properness proof. Their reviews do not turn sampled checks into proofs of universal identities or simplicity, and do not claim novelty or formal verification.

GPT-6.1 Terra reviewers [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the uniform two-prime extension at exact source `3b47eee4f5bfb43983b5ba474dff3689796eb9ad`. Both checked that the full-folder argument survives all field degrees, the eigenspace inequality replacing reciprocal-character inequivalence, all τ-stable normal-image cases, the trace Moufang witness, regular H action, scalar-generator and alternating-basis identifications, and order-based parameter separation. Their acceptances retain the previously reviewed folder, strict-defect and isotope interfaces, and cover this constructed family only. They do not classify other nilpotent-derived envelopes, establish literature novelty or provide formal verification; no new computation was used.
