# Monolithic odd folders with higher elementary-layer defect

**Continuation of 0323:C0010 [context outside this selected packet: `../claims/C0010.md`], with scoped independent reviews below.** The endpoint is a counterexample to the assertion that every finite simple proper odd Bol loop has a proper elementary τ-stable normal layer of defect one. The displayed construction gives a loop of order 3^149·7³ whose unique nontrivial elementary normal subgroup in its canonical envelope has defect two. The exact-source reviews below cover the Fourier-origin and outside-normalizer calculations and the full construction. It does not claim all odd loops are covered by any defect bound or that a quotient inverted set is a quotient-loop transversal.

The source interfaces are the full-inversion and strict-defect results in [odd-folder-radicals](odd-folder-radicals.md), independently reviewed at `95f226ac6c02b0153f3c226d823518e0891c1f1d` and `65a3e58df517df59656ab948ac9d122208f62c4a`, the elementary-layer conventions in [odd-elementary-layer-obstructions](odd-elementary-layer-obstructions.md), and the reviewed q=7 Schrödinger, Fourier and forbidden-line computations in [odd-monolithic-heisenberg-prime-family](odd-monolithic-heisenberg-prime-family.md). The prime-family theorem and its Fourier inputs were independently reviewed at `7171a4e11376839d09b2a76544fed0c941b2507e`, with analytic minor criteria at `123933cc594b601dd317d62b333a949d20431d35`. Properness uses [C0001, Lemma 1.2](../proofs/C0001.md#lemma-12-moufang-normalizer-and-primitivity-obstruction), reviewed at `9431ade99316d6bc62efb389492fef385b510b45`.

## Data and elementary layer

Let E=F_{3^6}, F₀=F_{3^3}, and let bar denote the nontrivial E/F₀ automorphism. Fix ζ∈E of order 7, put ξ=ζ−ζ⁻¹, and let R={1,2,4} and N=−R in F₇. Choose an F₀-line λF₀ outside the seven lines ξζ^kF₀. Such a line exists: E has 28 F₀-lines. Choose an F₃-line U<λF₀, and b₁,b₂∈λF₀ whose classes form an F₃-basis of λF₀/U.

Let T be the central product of two Heisenberg groups of order 7³, with a common central element z of order 7, generators x_i,y_i and relations [x_i,y_i]=z, with all mixed commutators trivial. Thus |T|=7⁵. Let A=<a₁,a₂>≅C₃², where a_i acts as x_i↦x_i², y_i↦y_i⁴, fixes the other factor and fixes z. Put L=T⋊A. Let θ swap x_i and y_i, invert z, and invert a_i; this is well-defined on the central product.

Let V=E^{F₇²}, with basis e_{j₁,j₂}, and let each T_i act by the q=7 diagonal-and-shift Schrödinger operators of the cited source, the two central actions being the same scalar ζ. Let a_i permute the corresponding index as in that source. Let σ be the tensor Fourier transform followed by bar. The source one-factor calculation gives σρ(l)σ=ρ(θl), and σ²=7²=1 in characteristic three. Set G=V⋊L and τ=(σ,θ).

The T-action is faithful: a nonzero shift changes a basis index, a nonzero diagonal coordinate gives a nonconstant diagonal, and a nonzero central coordinate acts as a nontrivial power of ζ. If an element ta of L acts trivially, its conjugation on T/Z(T) is trivial, forcing a=1, and then t=1. The independent diagonal operators have one-dimensional joint E-eigenspaces and the shifts act transitively on them, so V is irreducible over E. As ζ generates E over F₃, every F₃L-submodule is E-linear; V is also F₃-irreducible. Faithfulness now implies every nontrivial G-normal subgroup contains V, since a normal subgroup disjoint from V centralizes V. Hence G is monolithic, C_G(V)=V, and V is its unique minimal normal subgroup.

Put

    S={(i,j): i∈R, j∈F₇} ∪ {(0,j): j∈R} ∪ {(0,0)},
    W=Ue_{0,0} ⊕ ⊕_{(i,j)∈S−{(0,0)}} Ee_{i,j},
    H=<W,x₁,x₂,b₁e_{0,0}a₁,b₂e_{0,0}a₂>.

The displayed support has 25 points and is J=<x₁,x₂,A>-invariant; the origin graph is a subgroup because A fixes e_{0,0}. The quotient image H V/V is J. We have dim_F₃ V=294, dim V_+=147 by semilinear descent, and dim W=24·6+1=145. Consequently

    δ(V)=dim V_+−dim(H∩V)=2,
    |H|=3^147·7²=|C_G(τ)|,    [G:H]=3^149·7³.             (1)

For the equality H∩V=W, the two graph coefficients are independent modulo U and x₁,x₂ have order 7; the graph defines a homomorphism A→λF₀/U. Also |C_L(θ)|=7², since θ inverts A and fixes one dimension in each plane of T/Z while negating the center.

## Fourier support and all torus labels

Let A₀=(ζ^{ij})_{i∈N,j∈R}, F=(ζ^{ij})_{i,j∈F₇}. The cited q=7 computation gives A₀ invertible and A₀1=t1 with t≠0. Index rows by −(S−{0}) and columns by S−{0}. The block for first-coordinate N against R is A₀⊗F. Its Schur complement is

    (1−1ᵀA₀⁻¹1)A₀=A₀,

because 1ᵀ1=3=0 in E. Thus this 24×24 minor is invertible. Adjoining the origin row and column gives origin Schur complement 1 by the same calculation. Consequently E^S∩σ(E^S) is one-dimensional over E, its origin projection is injective, and on that line σ sends the origin coefficient c to bar(c). Heisenberg shifts translate S and multiply its basis coordinates by powers of ζ. The same row/column scaling gives the same minor and changes the induced origin action to c↦ζ^k bar(c). Therefore a σ-negative intersection vector has its origin coefficient in one of the seven excluded lines. The A-action preserves W. It follows that W avoids the negative space of every conjugate of σ by L. Outside involutions of G⋊<τhat> are G-conjugate to τhat, and conjugation by V does not change their action on V; hence

    W∩V_-^g=0 for every marked outside involution g.            (2)

We now test all possible nonidentity elements of H against the full product Λ² of marked outside involutions. Write the L-image as x₁^u x₂^v a, a=a₁^i a₂^j. On T/Z every conjugate of θ swaps the two axes in each plane, whereas L preserves each axis. Thus a nonzero x-exponent in an inactive coordinate prevents inversion. In the active coordinates conjugation by an appropriate x_i in H removes the x-exponent. If a=1, (2) and the same axis test rule out inversion. If a≠1 and h is inverted, then h³∈W is also inverted; (2) gives h³=1, so its cyclic cohomology class lies in H¹(<a>,V).

The a-orbits on the basis indices have size one or three. The latter give zero H¹; the fixed indices give the following complete list:

- If i,j are both nonzero, only (0,0) is fixed, and the actual H-class has coefficient in (i b₁+j b₂)+U⊂λF₀−{0}.
- If i≠0,j=0, all (0,t) are fixed and the actual H-class lies in ((i b₁)+U)e₀ ⊕ ⊕_{t∈R}Ee_t.
- If i=0,j≠0, all (t,0) are fixed and the corresponding class lies in ((j b₂)+U)e₀ ⊕ ⊕_{t∈R}Ee_t.

The V-component of an actual outside involution contributes a vector of the form (1−ρ(a⁻¹))v₀ when conjugating a lift of a; this is a coboundary and vanishes in H¹(<a>,V). Thus its induced action may be checked in the quotient extension L⋊<θ>. For an outside element t d θ, t∈T,d∈A, to normalize <a>, it must send a to a⁻¹, hence t∈C_T(a). This centralizer is the common center times the full Heisenberg groups of the inactive coordinates: active-plane eigenvalues 2^i and 4^i have no fixed vectors. On cohomology, full activity gives c↦ζ^k bar(c). For one inactive coordinate, the operator is the one-variable Fourier/conjugation operator followed by an inactive Heisenberg monomial and an A-permutation; the A-permutation preserves R and 0. Conjugation by a square root in A removes d while preserving the support and its origin coordinate. The remaining outside involution tθ is conjugate to θ inside the θ-stable inactive Heisenberg group, including the common center, by odd involution conjugacy. The cited q=7 translated-support calculation therefore applies to the entire partial-label support, including every arbitrary E-coefficient: a negative class has its origin coefficient in one of the seven excluded lines. The full-active formula gives the same conclusion. Thus

    H∩Λ²=1.                                                      (3)

This condition and |H|=|C_G(τ)| give the full odd Bol transversal, including all H-conjugates; they do not require a quotient loop.

## Normal subgroups and simplicity

Let N◁L be θ-stable. If N∩T=1, then [N,T]=1; C_L(T)=Z(T), so N=1. Otherwise N∩T contains Z(T). The four A-character lines of T/Z(T) are distinct and θ swaps the two in each coordinate plane. Hence N∩T is the full preimage of a sum of k∈{0,1,2} of these planes. If U_N≤A is the image of N, normality forces every plane on which U_N acts nontrivially to be selected, so s=dim_F₃U_N≤k. Modulo N∩T, projection of N to the inactive plane group is a homomorphism from the 3-group U_N to a 7-group, hence zero. Thus N=(N∩T)⋊U_N. Conversely these subgroups are normal and θ-stable. For k≥1,

    |C_N(θ)|=7^k,       |J∩N|=7^k 3^s.                           (4)

For N=1 or Z(T), both quantities are 1. Since H∩V=W, the strict-defect fixed/stabilizer ratio for the preimage of N is 3^{2−s}. If s=2, both planes are selected and N=L. Every proper preimage therefore has strict ratio greater than one. Monolithicity ensures every nontrivial normal subgroup of G contains V, so the reviewed strict-defect criterion gives simplicity using (3).

The subgroup generated by K maps onto L: its image contains A and the θ-commutator anti-diagonal in each plane; conjugation by a_i spans both axes, and their commutators generate z. Its normality and the irreducible faithful V-action then give V inside it. Monolithicity and W<V imply Core_G(H)=1, so this is the canonical generating envelope. The action on G/H is imprimitive because H<VH<G. The resulting simple loop is nonassociative because H≠1, and the cited C0001 primitivity lemma therefore excludes Moufangness without invoking a classification of finite simple Moufang loops.

Finally, every nontrivial elementary normal subgroup E₀ of G contains V. Since E₀ is abelian, E₀≤C_G(V)=V, so E₀=V. The unique candidate elementary τ-stable normal layer has defect 2 by (1), giving the stated counterexample under the independent review scope below.

## Higher-defect extension

**Extension included in the independent reviews below.** Let q≡7 mod 12 be prime, d=ord_q(3), m=d/2, and 1≤r≤m. Assume the one-factor Fourier minor M of the cited prime-family source is nonsingular. Its reviewed certificate establishes this hypothesis for q=7 and q=19, with m=3 and m=9 respectively. Take the central product of r order-q³ Heisenberg factors, all with the same center, and A=C₃^r acting in the corresponding independent planes. Choose κ∈F_q× of order 3; a_i sends x_i to x_i^κ and y_i to y_i^(κ⁻¹), fixes all other factors, and sends the i-th basis index j_i to κ⁻¹j_i. Since κ has odd order, it preserves the quadratic-residue support. Use E=F_{3^d}, F₀=F_{3^m}, the tensor Schrödinger representation on E^{F_q^r}, and the tensor Fourier involution followed by conjugation.

Let S_r consist of 0 and those nonzero index vectors whose first nonzero coordinate is a quadratic residue. Its size is (q^r+1)/2. Let W contain all E-coordinate lines at S_r−{0} and an F₃-subspace U of a good F₀-line at 0, where U has codimension r. Take r graph labels b_i whose images form a basis of that line modulo U, and take all x_i in the stabilizer. The elementary-layer defect is r, and the loop order is

    3^{m q^r+r} q^{r+1}.                                         (5)

The tensor minor has an inductive block proof. Put A₀=(ζ^{ij})_{i∈N,j∈R} and F_q=(ζ^{ij})_{i,j∈F_q}. The first block is A₀⊗F_q^{⊗(r−1)}. Its complement on the remaining indices is exactly the (r−1)-factor minor, because A₀1=t1, t≠0, and 1ᵀA₀⁻¹1=|R|/t=0 in characteristic three. The origin Schur complement is 1 at every step. Support translations and phases act by row and column scalings. For a nonzero torus label, cyclic cohomology retains the indices in its inactive coordinates, on which the restricted support is S_{r−k} for the number r−k of inactive factors; the same induction excludes negative classes with graph coefficient in the selected good line. For every active set, first remove the A-part of a normalizing outside involution by an A-square-root, which preserves the restricted support and origin, and then conjugate within the inactive central product by odd involution conjugacy. Active Fourier factors contribute 1 at the origin in cyclic cohomology. Thus the lower-rank support calculation applies to every coherent graph coefficient. The reviews below include this all-label induction.

For the normal-subgroup step, T/Z has r pairs of distinct A-characters, each pair exchanged by θ. A θ-stable normal subgroup contains the preimage of k complete coordinate planes; its A-image U_N is supported on those planes. The inactive projection is a homomorphism from the 3-group U_N to a q-group and vanishes. The fixed/stabilizer ratio is then 3^{r−dim U_N}, strictly greater than one unless U_N=A, which forces all planes and the whole quotient. The preceding argument gives a simple proper loop with V as the sole nontrivial elementary normal subgroup, now with defect r. This is not an unbounded-defect claim: the verified minor inputs give r≤3 for q=7 and r≤9 for q=19.

## Independent review

At exact source `b40066d01085772606b1d1160d58c033b8ba3302`, GPT-6.1 Terra reviewers [model reviewer identity omitted], [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the explicit defect-two construction and its conditional higher-defect extension. Their acceptance retains the reviewed prime-family Fourier-minor and translated-support inputs, the full odd-folder and strict-defect interfaces, and the elementary Moufang-primitivity obstruction. All checked the faithful central-product module, lexicographic minor and origin Schur complement, cyclic cohomology for every partial torus label, outside-normalizer and vector coboundary reductions, exhaustive invariant normal-subgroup lattice, strict ratios, canonical generation, core-freeness, properness and uniqueness of the elementary normal subgroup. No new computation or fresh primary-source audit was claimed. This establishes the stated finite-defect family under its hypotheses, not unbounded defect, infinitely many admissible primes, all-odd classification, novelty or formal verification.
