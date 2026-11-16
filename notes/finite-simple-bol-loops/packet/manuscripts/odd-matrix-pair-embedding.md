# Matrix-pair similarity inside simple odd Bol loops

**Continuation of 0323:C0010 [context outside this selected packet: `../claims/C0010.md`], with exact-source reviews below.** This gives an explicit uniform embedding of simultaneous similarity of two matrices over Fp into isomorphism of the simple proper odd Bol G-loops in the [alternating-form family](odd-alternating-form-family.md), whose construction and isomorphism criterion were reviewed at exact source `2a25b81e3efe5bdd8a3923e27c94aef16a559094`. The present embedding has the separate mathematical reviews recorded below. It makes no complexity-class hardness assertion and does not classify all simple Bol loops.

## Theorem and construction

Fix odd primes p,q with p dividing q−1, and put r=ord_q(p) and E=F_(p^r). For every n≥1, an explicit construction associates to each pair (A,B)∈M_n(Fp)² a simple proper odd Bol G-loop L(A,B) of order

    p^[r(44n+22)+5] q^11,                                  (1)

such that

    L(A,B) ≅ L(A′,B′)
      iff there is S∈GL_n(Fp) with A′=SAS^−1 and B′=SBS^−1.  (2)

The construction outputs five alternating matrices of size 44n+22 over Fp, interpreted as E-matrices and passed to the reviewed family with k=5. Thus, for fixed p,q, the matrix-data output has polynomial size in n; this is a compact parameter encoding, not an explicit multiplication table for the loop.

Let U=Fp^n⊕Fp^n. Write P=diag(I_n,0), and put

    D=[[0,I_n],[0,0]],   D_A=[[0,A],[0,0]],   D_B=[[0,B],[0,0]].

On X=U⊕U*, use the ordered coordinates (U₁,U₂,U₁*,U₂*) and define

    J=[[0,I_(2n)],[-I_(2n),0]],   F(T)=diag(T,Tᵀ).         (3)

The four matrices JF(P), JF(D), JF(D_A), JF(D_B) are alternating. No multiplicativity of F is asserted.

For i=1,2,3,4 put dᵢ=i(2n+1). Add symplectic spaces C₀,C₁,…,C₄, with dim C₀=2 and dim Cᵢ=2dᵢ. Let C be their direct sum. The five output forms on X⊕C are:

* B₀: J on X and the standard symplectic form on every Cᵢ;
* Bᵢ, for i=1,2,3,4: respectively JF(P), JF(D), JF(D_A), JF(D_B) on X, the standard symplectic form on Cᵢ, and zero on all other marker spaces.

Their common radical is zero because B₀ is nonsingular. They are Fp-linearly independent: restriction of a relation to C₀ forces the coefficient of B₀ to vanish, then restriction to each Cᵢ forces the coefficient of Bᵢ to vanish. The total dimension is

    dim(X⊕C)=4n+2+2Σ_(i=1)^4 i(2n+1)=44n+22.

The tuple meets the reviewed family's input hypotheses. Its order is therefore (1).

## The active tuple recovers the pair

Suppose first that the five active forms J, JF(P), JF(D), JF(D_A), JF(D_B) are matched in their given order by a congruence. Since J is nonsingular, the congruence intertwines the four operators F(P),F(D),F(D_A),F(D_B).

Set X₂=ker F(P), and K=ker(F(D)|X₂). In the ordered coordinates (U₁,U₂,U₁*,U₂*), one has X₂=U₂⊕U₂* and K=U₂*. The map F(D) induces an isomorphism

    X₂/K → im(F(D)|X₂)=U₁.

Both F(D_A) and F(D_B) vanish on K and map X₂ into U₁. Composing the induced maps X₂/K→U₁ with the inverse of the induced F(D) map recovers A and B, respectively, on X₂/K≅Fp^n. These subspaces and maps are intrinsic to the four operators. Thus an intertwiner yields simultaneous similarity of the original ordered pair, with no transpose or dual ambiguity. The argument works over every extension field.

Conversely, if A′=SAS^−1 and B′=SBS^−1, put T=diag(S,S) on U and L_X=diag(T,T^−ᵀ) on U⊕U*. Then L_XᵀJL_X=J and, for each of the four active forms,

    L_Xᵀ (JF(M′)) L_X = JF(M),

where M runs through P,D,D_A,D_B and M′ is its primed counterpart. This proves the converse active congruence with the indicated orientation.

## Removing permutations and cancelling markers

For i=1,…,4 the rank of Bᵢ lies in the interval [2dᵢ,2dᵢ+4n]. Consecutive intervals are disjoint because 2(dᵢ₊₁−dᵢ)=4n+2. The rank of B₀ is 44n+22, larger than the upper endpoint for B₄, namely 20n+8. Thus any congruence of the unordered five-form tuples fixes every label by rank.

With B₀ fixed, write Bᵢ=B₀Tᵢ. A labeled congruence induces simultaneous similarity of the four operators Tᵢ. Their module on X⊕C splits as the active module M(A,B) on X and a fixed marker module C, independent of (A,B). If two output tuples are congruent, then

    M(A,B)⊕C ≅ M(A′,B′)⊕C.                               (4)

The modules are finite-dimensional modules over the free associative algebra on four generators. They have finite length, so the Krull–Schmidt cancellation argument below applies to (4). Hence M(A,B)≅M(A′,B′); the intrinsic quotient above gives simultaneous similarity of (A,B) and (A′,B′). Conversely, the active congruence from S extends by the identity on C. This proves the iff statement for tuple congruence over any field extension of Fp.

For completeness, the required cancellation is purely finite-dimensional. Every module decomposes into indecomposables by induction on dimension. For an endomorphism f of an indecomposable module, stabilization of kernels and images gives the Fitting decomposition ker(f^a)⊕im(f^a) for sufficiently large a. Both are submodules, so f is either invertible or nilpotent; in the latter case 1−f is invertible. Thus the nonunits of its endomorphism ring form an ideal: multiplying a nonunit by any endomorphism cannot make it invertible in finite dimension, and if two nonunits had an invertible sum, multiplication by the inverse sum would contradict the fact that f or 1−f is invertible. The endomorphism ring is therefore local.

Given two indecomposable decompositions of one module, the identity on a summand A is the sum of the maps obtained by inclusion, projection to each summand B of the other decomposition, and projection back to A. Locality forces one of these maps to be invertible. Hence A is a direct summand of that B, and indecomposability makes A≅B. The usual block elimination of an isomorphism with this invertible component identifies the complementary sums (its Schur complement is an isomorphism). Induction yields equality of all indecomposable multiplicities. This proves both cancellation of a common direct summand in (4) and cancellation of equal positive multiples used below, for the finite-dimensional modules over either free algebra appearing here.

## Galois action and descent

All output matrices have entries in Fp. Consequently every θ∈Gal(E/Fp) fixes every output matrix entrywise. The reviewed family criterion, including its possible coordinate permutation, therefore reduces loop isomorphism to E-congruence of the five tuples, and the rank calculation removes the permutation.

If the tuples are E-congruent, the preceding section gives an E-linear simultaneous similarity of the two Fp-defined pairs. Restriction of scalars turns that similarity into an Fp-module isomorphism

    M_pair(A,B)^r ≅ M_pair(A′,B′)^r.

Krull–Schmidt cancellation gives M_pair(A,B)≅M_pair(A′,B′) over Fp, which is exactly simultaneous similarity by a matrix S∈GL_n(Fp). The converse follows by scalar extension and the explicit congruence above. Applying the reviewed family isomorphism theorem proves (2), conditional on that interface.

At exact source `52fe4d027acd8a70f2872a19971c6c0e5cbbeb42`, GPT-6.1 Terra reviewers [model reviewer identity omitted], [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the full embedding conditional on the alternating-form family and its strict loop-isomorphism criterion. They checked the alternating forms, independent markers, disjoint rank intervals, ordered-pair recovery without dual ambiguity, the symplectic converse, ordinary module cancellation rather than an assumed symplectic cancellation, the inline finite-dimensional Krull–Schmidt argument, scalar descent and the dimension/order formulas. The family source is pinned at `2a25b81e3efe5bdd8a3923e27c94aef16a559094`; its later review-delivery commit is `825681f0ee689b3e20c82ce2e297a6e5c74cd4d2`. The historical source itself correctly said review pending. [model reviewer identity omitted] treated the family as a conditional input and did not independently verify that later attribution. No computation, formal verification or new primary-source audit was performed. The conclusion is the exact orbit embedding, not a complexity-class hardness assertion or unrestricted loop classification.
