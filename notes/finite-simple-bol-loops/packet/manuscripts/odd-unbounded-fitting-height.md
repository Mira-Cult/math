# Odd simple Bol loops of unbounded Fitting height

**Continuation of 0323:C0010 [context outside this selected packet: `../claims/C0010.md`], with the exact-source reviews recorded below.** For every h≥0, the construction gives a finite simple proper odd left Bol loop whose canonical left multiplication group has Fitting height h+3, under the cited folder inputs. Fitting height is the minimum length of a normal series with nilpotent factors; it is distinct from derived length. The construction uses iterated regular wreath products and an affine exact factorization, not loop-table enumeration. Its endpoint is unboundedness, not an isomorphism census or exhaustive classification.

The exact-factorization folder, generated faithful group and properness interface is [C0002, Proposition 1.1](../proofs/C0002.md), at historical source `9431ade99316d6bc62efb389492fef385b510b45`, with the C0001 canonical-folder and simple-Moufang primitivity inputs specified there. The simplicity proof below uses the separately reviewed odd τ-normal strict-defect criterion at `65a3e58df517df59656ab948ac9d122208f62c4a` in [odd-folder-radicals.md](odd-folder-radicals.md), rather than assuming a simple quotient is the whole loop. It generalizes the [reviewed Q_{p,q} group calculation](odd-stabilizer-alignment.md#the-known-simple-family-realizes-the-orbit-obstruction) at `9d806247691956ef2dfb7a39ff32fe2934fde351`; that source is context, not a review of the new construction.

## Odd monomial groups of increasing height

Fix p=7, q=29 and E=F_{7⁷}. The prime q has ord_q(7)=7, since 7⁷−1=6·29·4733 and 7 is not 1 modulo 29. Choose distinct primes r₁,…,r_h, all congruent to 1 modulo 7 and distinct from 7,q. They exist elementarily: given finitely many forbidden primes, take a=7 times their product. Every prime divisor ℓ of Φ₇(a)=1+a+⋯+a⁶ is new and different from 7; ord_ℓ(a)=7, so ℓ≡1 mod 7. Pick k_i∈F_{r_i}× of order 7.

Set U₀=1 and recursively define the regular wreath product

    U_i = C_{r_i} wr U_{i−1} = C_{r_i}^{U_{i−1}} ⋊ U_{i−1}.

Define an automorphism ψ_i of order 7 recursively: on U_{i−1} use ψ_{i−1}; on a base function b:U_{i−1}→C_{r_i}, set

    (ψ_i b)(u) = b(ψ_{i−1}^{−1}u)^{k_i}.

For U₀ the automorphism is identity; ψ₁ is the nontrivial power map k₁. Whenever U₀⋊<ψ₀> occurs, the bracket denotes a formal C7 acting trivially, not the trivial subgroup of Aut(U₀). The definition respects the regular translation action. Its seventh power is identity, and it is nontrivial for i≥1. Since the coinvariants of a regular permutation base are C_{r_i},

    U_i,ab ≅ C_{r_i}×U_{i−1,ab},

and ψ_i acts on each cyclic factor by the corresponding k_j. Thus ψ_i−1 is invertible on U_i,ab.

The action of U_{i−1}⋊<ψ_{i−1}> on the new base is faithful: an element uψ^j acts by a regular coordinate permutation followed by scalar k_i^j. Identity forces j=0 and then u=1. Since r_i divides none of the previous groups, the Fitting subgroup of U_i⋊<ψ_i> is precisely its r_i-base: any nilpotent normal subgroup centralizes the base in all other prime components, and the displayed action has trivial centralizer. Therefore

    h_F(U_i⋊<ψ_i>)=i+1.                                      (1)

For i=0 this says h_F(C7)=1; the same reasoning without ψ gives h_F(U_i)=i for i≥1.

## Monomial affine group and exact factorization

Put U=U_h, ψ=ψ_h, Q=C_q^U, and T=Q⋊U using the regular action. Let V=E^U as an F7-vector space. Q acts by independent q-th-root scalars on coordinates and U by the regular coordinate permutation. Each coordinate is an irreducible 7-dimensional F7 C_q-module, the coordinate modules are pairwise nonisomorphic for Q, and U acts transitively on them. Therefore V is a faithful irreducible F7 T-module.

Let φ apply field Frobenius a↦a⁷ to each coordinate and permute indices by ψ. Then φ normalizes T, induces ψ on U and the power map 7 plus index permutation on Q, and has order 7. In the special case h=0, the index permutation is trivial and φ is the field Frobenius. The group

    T_ab ≅ C_q × U_ab

has φ acting on its C_q factor by seventh power and on the others by k_i. Thus φ−1 is invertible on T_ab. For any 1≤i<7 and t∈T, the automorphism α=inn(t)φ^i has the same fixed-point-free action on T_ab. The subgroup [T,α] is normal in T; in T/[T,α], α acts trivially, so its abelianization is both a quotient of T_ab and fixed by α. It is trivial. As T is solvable, the quotient is trivial; hence

    [T,inn(t)φ^i]=T.                                         (2)

Set X=V⋊(T⋊<φ>). Equation (2) gives X′=V⋊T and X/X′≅C7. Let Y1=T⋊<φ>. Choose a φ-invariant F7-hyperplane W containing (φ−1)V and v∉W; it exists because a 7-element in characteristic 7 has nonzero fixed quotient. Put g=(v,φ) and Y0=⟨W,g⟩. Since the norm 1+φ+⋯+φ⁶=(φ−1)⁶, g⁷∈W and |Y0|=|V|. For 1≤i<7, every element w g^i has translation component congruent to i v mod W, whereas (1−φ^i)V⊆W, so it has no fixed point on V. Nonzero translations in W have none. Hence Y0 is regular on V and

    X=Y0Y1,  Y0∩Y1=1,  X′Y0=X′Y1=X.                         (3)

The action of T⋊<φ> on V is faithful: a trivial monomial transformation has trivial index permutation and all q-scalars trivial, while a nonzero φ power induces nontrivial Frobenius and hence cannot be canceled by scalar multiplication. Therefore C_X(V)=V and V is a minimal normal subgroup. Y1 is corefree by the faithful affine action. A nontrivial normal subgroup inside Y0 would meet V and contain V, impossible since |Y0|=|V| and Y0≠V. Thus Y0 is corefree too. By the cited exact-factorization interface the canonical faithful generated folder has

    G={(x,y)∈X²:xy∈X′},  H=G∩(Y0×Y1),
    K={(x,x⁻¹):x∈X},     τ(x,y)=(y,x).

The resulting loop has odd order |X|. Its canonical stabilizer has order |X′|>1, so the loop is nonassociative. Properness follows after the simplicity check below. The full multiplication group is not being identified with G.

## Simplicity without quotient-folder assumptions

Put M=V×V. As the affine complement acts faithfully, C_G(M)=M. The two V coordinates are pairwise nonisomorphic irreducible T²-modules, and |T| is prime to 7 because all the selected primes differ from 7. Every nonzero normal subgroup of G meets M; a τ-stable one therefore contains all M by semisimplicity and the coordinate swap.

Modulo M,

    G/M=(T×T)⋊<t>,  t=(φ,φ⁻¹),
    HM/M={ (φ^i,aφ⁻i) : a∈T, i∈F7 }.

Let 1≠N◁G be τ-stable. If its image Nbar modulo M contains an element with nonzero t exponent, equation (2), applied separately to the two coordinates, shows commutators with T×T generate T×T. Then Nbar is all of G/M and N=G. Thus for a proper N, Nbar≤T×T. Its two coordinate projections agree by τ-invariance; write this subgroup as R≤T. We do not assume Nbar=R×R. The displayed H image gives

    [G:HN]=[T:R].

If two diagonal-inverse section elements have equal image modulo N, their first coordinates differ by an element of V⋊R. Consequently

    |KN/N|≥[X:V⋊R]=7[T:R]>[G:HN].

The reviewed odd τ-stable-normal strict-defect criterion implies simplicity: because fixed points lift in this odd group, |KN/N|/[G:HN]=|C_N(τ)|/|H∩N|. No projection of K to a normal quotient is assumed to be a loop transversal.

For properness, the nontrivial normal subgroup X′×1 of G has its identity orbit contained in the section points indexed by Y1, a proper subset of X. Indeed (x,x⁻¹)∈(X′×1)H forces x⁻¹∈Y1. The faithful action makes this normal subgroup's orbit nontrivial; hence canonical LMlt is imprimitive. The C0001 simple-Moufang primitivity input used in C0002 Proposition 1.1(3) then excludes Moufang. This is the explicit properness interface, not an inference from solvability alone.

## Fitting height

In L=T⋊<φ>, the action of U⋊<φ> on Q is faithful: U acts by regular coordinate permutations and a nonzero φ power applies the nontrivial seventh-power scalar automorphism on each C_q. As q is new to U and 7, the same nilpotent-normal-centralizer argument as in (1) gives Fit(L)=Q. By (1),

    h_F(L)=h+2.

Also O_7(L)=1: a normal 7-subgroup centralizes the normal q-subgroup Q and hence lies in C_L(Q)=Q. In X=V⋊L the Fitting subgroup contains V; its non-7 components centralize V and are trivial because C_X(V)=V, while its 7-component has no nontrivial image in L. Thus Fit(X)=V and h_F(X)=h+3.

The canonical folder group G is a subgroup of X×X projecting onto X. Fitting height does not increase under subgroups or quotients of finite solvable groups, so h_F(G)=h_F(X)=h+3. As h is arbitrary this proves, subject to the stated inputs, unbounded Fitting height of canonical LMlt among finite simple proper odd Bol loops. It does not claim an exhaustion theorem or novelty. No computation, formal verification or fresh primary-source audit is claimed.

At exact source `feaf33e8b9f2725ac9b835a49dca95de4332171d`, GPT-6.1 Terra reviewers [model reviewer identity omitted], [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the full construction under the cited exact-factorization, canonical-folder, odd strict-defect and simple-Moufang primitivity interfaces. Their reviews covered the wreath automorphisms and faithful actions, fixed-point-free abelianization argument, affine regular factorization, every relevant τ-stable normal subgroup, properness interface and exact Fitting-height calculation. These are mathematical model reviews at that source, not fresh primary-source audits, computational tests or formal verification.
