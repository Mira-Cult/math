# A conditional prime family of monolithic odd Bol folders

**Manuscript-local continuation of 0323:C0010 [context outside this selected packet: `../claims/C0010.md`], with the scoped reviews below.** Let q be a prime with q≡7 mod 12, put d=ord_q(3), n=(q−1)/2, E=F_{3^d}, F₀=F_{3^{d/2}}, and choose ζ∈E of order q. Let R and N be the nonzero quadratic residues and nonresidues modulo q. Assume:

The base n×n Fourier matrix

    M=(ζ^{ij})_{i∈N, j∈R}                                  (1)

is nonsingular over E. The shifted matrix with entries ζ^{(i+t)j} is obtained from M by multiplying column j by ζ^{tj}, so all shifts are equivalent to this single condition.

Under the odd-folder and strict-defect interfaces cited below, this condition gives a finite simple **proper** left Bol loop of order 3^{qd/2+1}q² whose canonical left multiplication group is monolithic. The proof gives all displayed stabilizer choices and an exact Frobenius² isomorphism relation within this family; it does not classify arbitrary stabilizers. The exact calculation below verifies the hypothesis for q=19, giving order 3¹⁷²·19². No infinitude of qualifying primes is claimed. The independently reviewed q=7 example is [odd-monolithic-heisenberg-construction](odd-monolithic-heisenberg-construction.md), at `bb8b8a6048ab6c7fa1acc715764eb5da15bf5358`; it uses an explicit stabilizer; the present argument also covers q=7 under (1).

The odd full-inverted-set, outside-involution conjugacy and strict-defect interfaces are in [odd-folder-radicals](odd-folder-radicals.md), with full-inversion review `95f226ac6c02b0153f3c226d823518e0891c1f1d` and strict-defect pin `65a3e58df517df59656ab948ac9d122208f62c4a`. Properness below uses [C0001, Lemma 1.2](../proofs/C0001.md#lemma-12-moufang-normalizer-and-primitivity-obstruction), reviewed at `9431ade99316d6bc62efb389492fef385b510b45`; this step does not invoke the finite simple Moufang classification. The conditional construction and exact-isomorphism theorem have the reviews below; subsequent minor nonvanishing deductions have separate status.

## Group and module

The congruence q≡7 mod 12 gives q≡1 mod 3 and makes 3 a quadratic nonresidue modulo q. Thus d is even and 3^{d/2}≡−1 mod q. In particular E=F₃(ζ), and the nontrivial E/F₀ automorphism is ̄c=c^{3^{d/2}}, with ̄ζ=ζ⁻¹.

Let T be the order-q³ Heisenberg group on x,y,z, with z central and [x,y]=z. Let A=⟨a⟩≅C₃ act by a x a⁻¹=x^r, a y a⁻¹=y^{r⁻¹}, a z a⁻¹=z, where r has order 3 in F_q×. Set L=T⋊A. Let θ swap x and y, invert z, and invert a. On V=E^q, with indices j modulo q, put

    x e_j=ζ^j e_j,   y e_j=e_{j+1},   z e_j=ζ e_j,   a e_j=e_{r⁻¹j},
    (σv)_i=Σ_j ζ^{ij} ̄v_j.                                (2)

Fourier orthogonality gives σ²=q·id=id in characteristic 3, and direct substitution gives σρ(l)σ=ρ(θl). The center acts by ζ and E=F₃(ζ); the x-eigenspaces are the E e_j and y permutes them transitively. Hence V is a faithful irreducible F₃L-module. Put G=V⋊L and τ=(σ,θ). Every nontrivial normal subgroup of G contains V: if it misses V, it centralizes V, and faithfulness makes it trivial. Thus G is monolithic with socle V.

Since r has odd order, it is a square in F_q×; it preserves R. For an F₀-line λF₀⊂E choose an F₃-hyperplane U<λF₀ and b∈λF₀\U. Set

    S=E e₀ ⊕ ⊕_{j∈R} E e_j,  W=U e₀ ⊕ ⊕_{j∈R} E e_j,
    H=⟨W, x, (b e₀,a)⟩.                                 (3)

Both x and a fix b e₀ and normalize W, so H/W≅J=⟨x,a⟩. The F₃-dimension of V_+ is qd/2: on any odd-dimensional E-space, an F₀-semilinear involution has an F₀-fixed form by descent. Moreover dim W=nd+d/2−1=qd/2−1, so |H|=3^{qd/2}q. The centralizer C_L(θ) has order q, hence |C_G(τ)|=|H|.

## Gaussian periods and the exact bad lines

Write s=Σ_{r∈R}ζ^r, t=Σ_{j∈N}ζ^j and let χ be the quadratic character of F_q, extended by χ(0)=0. Since R and N partition F_q×, s+t=−1. We derive st=(q+1)/4 directly. Put G=s−t=Σ_x χ(x)ζ^x. For a≠0,

    Σ_x χ(x)χ(x+a)=−1.

Indeed scaling reduces to a=1; the number of pairs (x,y) with y²=x(x+1) is q−1, since (2x+1−2y)(2x+1+2y)=1 and each nonzero first factor determines the pair. It is also q+Σ_x χ(x(x+1)), proving the sum. Therefore

    G²=χ(−1)Σ_a ζ^a Σ_x χ(x)χ(x+a)=−q,

using χ(−1)=−1. Thus 4st=(s+t)²−(s−t)²=1+q. All integer identities are interpreted in E. Since q≡7 mod 12, n=(q−1)/2=0 in F₃ and st=(q+1)/4=−1 in E.

Every outside involution of G⋊⟨τhat⟩ is G-conjugate to τhat. Conjugation by V does not change its action on V, and A normalizes S and fixes the e₀-coordinate. Consider ordered g=x^u y^v z^k∈T, and write w=ρ(g)h for h∈S. Its support is {v}∪(v+R). To have σw supported there, the N-index equations are solved by

    bar(w_{v+r})=s ζ^{−vr} bar(w_v),  r∈R.                 (4)

Indeed for each j∈N, the relevant character sum is Σ_{r∈R}ζ^{jr}=t, giving 1+st=0. The R-column coefficient matrix is a shifted version of M, up to nonzero row scalings. Hypothesis (1) makes this solution unique once w_v is fixed. The support intersection is therefore a one-dimensional E-space, and projection to w_v is injective. This space is σ-stable, since σ²=1; at coordinate v, (4) gives

    (σw)_v=(1+ns)ζ^{v²}bar(w_v)=ζ^{v²}bar(w_v).

Thus σw=−w precisely when bar(w_v)=−ζ^{−v²}w_v. Let ξ=ζ−ζ⁻¹, so bar(ξ)=−ξ. As w_v=ζ^{k+uv}h₀, the possible e₀-coordinates h₀ form exactly

    ξ ζ^{v²/2−k−uv} F₀.                                    (5)

As g varies, these are precisely the q lines ξζ^jF₀. Consequently, if λF₀ is outside those lines, W meets no negative eigenspace of any marked outside involution:

    W∩V_-^g=0 for every g∈G.                               (6)

The same q lines arise from the order-three cohomology calculation. On each nonzero A-orbit of indices the module is a regular F₃[A]-module, while A fixes E e₀. Hence H¹(A,V)=E e₀. On this cohomology σ induces bar: Fourier sends e₀ to the all-one vector, and the sums over the nonzero A-orbits are norms. The normalizer of A in L is Z(T)×A, since A is fixed-point-free on T/Z(T). If an order-three element above a is inverted by an outside involution, that involution normalizes A after projection; its induced action on H¹(A,V) is c↦ζ^j bar(c) for some j. Inversion requires c=−ζ^j bar(c), whose solutions are exactly the q lines in (5), since 2 is invertible modulo q.

The number of F₀-lines in E is 3^{d/2}+1. It is divisible by q because 3^{d/2}≡−1 mod q; it is even and q is odd, so it is at least 2q. Hence a line λF₀ outside the q forbidden lines always exists. For this choice (6) holds, and every nonzero element of b+U lies outside the order-three real-class lines. No growth estimate or additional numerical hypothesis is needed.

## Folder, simplicity and properness

Let Λ be the outside involutions and K={g∈G:τ(g)=g⁻¹}. We show H∩Λ²=1. In odd G, Λ is one G-conjugacy class, and an element of Λ² is inverted by an outside involution. If h∈H has identity image in L, then h∈W and (6) rules it out. If its image is a nontrivial x-power, no outside involution can invert it: on T/Z(T), every conjugate of θ exchanges the two axes, while L preserves each axis. Finally, if its image has nonzero A-label, that image has order 3. If h³≠1, then h³∈W is inverted by the same outside involution, contradicting (6). If h³=1, conjugate its image inside J to a or a⁻¹. Its normalized H¹-class lies in b+U, whereas (5) would put it in a forbidden line. Thus h=1.

The full-inverted-set interface gives K⁻¹K=K²=Λ², so K is a transversal to H and all its conjugates and defines a left Bol folder. It generates G: its image in L contains A and a nonzero anti-diagonal vector of T/Z(T); the A-translates of that vector span both axes, and their commutator gives Z(T). The subgroup ⟨K⟩=[G,τ] is normal in G by the odd full-inverted-set interface. Its commutators with the irreducible faithful module V therefore generate V inside ⟨K⟩. Since H∩V=W<V, monolithicity gives Core_G(H)=1. The resulting G is therefore the canonical left multiplication group.

The θ-stable normal subgroups of L are 1,Z(T),T,L. Nontrivial normal subgroups contained in T contain its center; the only nonzero proper A-invariant subspaces of T/Z(T) are the two axes, interchanged by θ. A normal subgroup with nontrivial A-image contains T. It follows that the nontrivial proper τ-stable normal subgroups of G are V,VZ(T),VT. Their respective fixed/stabilizer ratios |C_N(τ)|/|H∩N| are all 3: the quotient fixed-point orders are 1,1,q and the corresponding stabilizer intersections modulo W have orders 1,1,q. The cited strict-defect criterion gives simplicity. The loop order is

    [G:H]=3^{qd/2+1}q².                                    (7)

The loop is nonassociative because H≠1. Furthermore H<VH<G, so the faithful transitive G-action on G/H is imprimitive. The reviewed C0001 Lemma 1.2 says that a simple nonassociative Moufang loop has primitive left multiplication group. This contradiction proves the constructed loop is proper, without CFSG or a simple Moufang classification.

## Isomorphism classes within this family

For fixed q and an allowed line M=λF₀, all choices of U and b in (3) produce isomorphic loops. Multiplication by F₀× commutes with L and σ. It acts transitively on F₃-hyperplanes of M: the nondegenerate trace pairing writes every hyperplane as the kernel of Tr_{F₀/F₃}(cx) for some c∈F₀×. For a fixed U, the two nonzero cosets of U are exchanged by −1, and H depends only on b+U.

For each even j modulo d, let c∈R be the unique quadratic-residue square root of 3^j in F_q×. Existence follows because 3^j is a square; uniqueness follows from q≡3 mod 4, which makes −1 a nonresidue. The map

    Φ_j(Σ_i v_i e_i)=Σ_i v_i^{3^j} e_{ci}                  (8)

commutes with σ, intertwines the quotient automorphism x↦x^c, y↦y^c, z↦z^{c²}, a↦a, and preserves the R-support. Thus it carries an allowed line M to M^{3^j}. In particular lines in the same Frobenius²-orbit give isomorphic loops.

Conversely, an isomorphism of these loops induces an isomorphism of canonical folders and commutes with τ, because K generates and τ is characterized by inversion on K. The monolith V is characteristic. Every complement to V in G is V-conjugate to L: H¹(L,V)=0, since T is a normal p′-subgroup and V^T=0, by coprime averaging and inflation-restriction. After a V-conjugation, the isomorphism has the form Inn(v)∘(F,φ), with φ∈Aut(L) and F intertwining the actions. Conjugation by V leaves W and the image J of H unchanged; hence φ(J)=J. The induced quotient map φ commutes with θ, and F commutes with σ.

The characteristic q-core of J is ⟨x⟩, so φ(x)=x^c for some c∈F_q×. Commutation with θ gives φ(y)=y^c and φ(z)=z^{c²}. Writing φ(a)=x^u a^i, its action on x forces i=1, and commutation with θ then forces u=0. Since z acts as ζ, F is semilinear over E with Frobenius exponent j satisfying 3^j=c². The x-eigenlines and y-shift force F to have the form (8), up to a common scalar h∈E×; Fσ=σF forces h∈F₀×. The nonzero-axis support of W must map to R, so cR=R and c∈R. The e₀ component of F(W)=W′ now gives M′=M^{3^j}. As 3 is a quadratic nonresidue, 3^j=c² forces j even. Therefore the Frobenius²-orbits on the allowed lines are exactly the loop-isomorphism classes **within this family**. This does not classify arbitrary stabilizers in the same envelope.

Let m=d/2 and Q=3^m+1. The cyclic group D=E×/F₀× has order Q, and the allowed lines are D minus ξ⟨ζ⟩. The class of ξ has order 2: bar(ξ)=−ξ, so ξ²∈F₀ while ξ∉F₀. Thus it is fixed by every power of 9, and Burnside's lemma gives the exact number

    (1/m) Σ_{k=0}^{m−1} [gcd(9^k−1,Q)−gcd(9^k−1,q)].       (9)

For q=7 this is 9, agreeing with the separately reviewed line family at `bb3b8f4cef211caed242d3884c8b7b10a3544d2f`; for q=19 the nine summands are 19665,3,3,27,3,3,27,3,3, giving **2193** isomorphism classes. The standalone arithmetic certificate checks both evaluations. These isomorphism and counting deductions have the exact-source reviews below.

## Exact minor controls and scope

For q=7 and q=19, 3 has order q−1. The standalone standard-library certificate [verify_odd_heisenberg_prime_minors.py](../code/verify_odd_heisenberg_prime_minors.py) verifies these orders and computes the base matrix (1) over F₃[X]/Φ_q, using exact integer arithmetic. With Python 3.11+ and assertions enabled it reports base ranks 3 and 9 respectively. Because the shifted matrices differ by invertible column scalings, those two rank checks cover every shift. The q=19 output gives the stated order 3¹⁷²·19². The certificate also checks the Gaussian periods, all translated support equations and both Burnside evaluations. Root read and ran this exact source with Python 3.12.14; all assertions passed.

The conditional construction has independent model reviews and finite arithmetic controls. It does not establish the base-minor condition for all q≡7 mod 12, prove that infinitely many primes qualify, or classify stabilizers outside the displayed family.

## A group-algebra criterion for the Fourier minor

**Independently reviewed continuation of the preceding theorem at exact source `7171a4e11376839d09b2a76544fed0c941b2507e`.** Retain its prime q≡7 mod 12 and notation E, ζ, R and N. Since −1 is a quadratic nonresidue, N=−R. Let n=|R|=3^a m with 3∤m, and choose a generator g of the cyclic group R. Define

    F(X)=Σ_{k=0}^{n−1} ζ^{−g^k} X^k ∈ E[X].                 (10)

Then the base Fourier minor M in (1) is nonsingular if and only if

    gcd(F(X), X^m−1)=1 in E[X].                             (11)

Equivalently, for every character χ:R→Ebar× of order prime to 3,

    Σ_{r∈R} χ(r) ζ^{−r} ≠ 0.                               (12)

To see this, index the rows of M by i=−r⁻¹ and its columns by j=s, with r,s∈R. Its entry is ζ^{−r⁻¹s}. Thus, up to the displayed row permutation and the harmless transpose determined by the left/right convention, M is the regular convolution matrix of

    f=Σ_{r∈R} ζ^{−r}[r] ∈ E[R].                            (13)

It is nonsingular exactly when f is a unit of E[R]. The generator g identifies E[R] with E[X]/(X^n−1); in characteristic 3,

    X^n−1=(X^m−1)^{3^a}.

The unit criterion in this quotient is precisely (11). After extending scalars to Ebar, the roots of X^m−1 are distinct and correspond to the characters in (12). Equivalently, the determinant, up to the sign of the row and column permutations, is the product of the sums in (12), each with multiplicity 3^a. This explicitly accounts for the modular multiplicity; it does not assume that X^n−1 has n distinct roots.

**Corollary.** If q=2·3^a+1 is prime, a≥1, then the Fourier-minor hypothesis (1) holds. Indeed n=3^a, so m=1 and (11) reduces to F(1)≠0. Here

    F(1)=Σ_{r∈R}ζ^{−r}=Σ_{j∈N}ζ^j=t,

and the Gaussian-period identity st=−1 proved above gives t≠0. Such a prime satisfies q≡7 mod 12, so the preceding construction, properness and within-family isomorphism theorem apply without a separate minor computation. This includes q=7 and q=19, but does not assert that infinitely many primes of this form exist. For m>1, (11)–(12) are an exact character-sum criterion; their general nonvanishing is not claimed.

**Odd-Frobenius nonvanishing.** More generally, suppose the order of 3 modulo m is odd, with the convention that the order modulo 1 is 1. Then (12) holds for every character, and the Fourier minor is nonsingular. This includes m=1. The condition is sufficient, not claimed necessary.

For the proof, let χ:R→Ebar× have order ℓ dividing m. If χ is trivial, (12) is the period t≠0 already proved. Otherwise ord_ℓ(3) is odd, because it divides the odd order modulo m. Choose an odd positive h with 3^h≡1 mod ℓ and put

    Aχ=Σ_{r∈R}χ(r)ζ^r,       Bχ=Σ_{r∈R}χ(r)ζ^(−r).

Suppose Bχ=0. Both 3 and −1 are quadratic nonresidues modulo q, so −3^h∈R. Applying Frobenius^h, which fixes the χ-values, and substituting t=−3^h r gives

    0=Bχ^{3^h}=χ((−3^h)⁻¹) Aχ.

The scalar is nonzero, so Aχ=0 too. Since |R|=(q−1)/2 is odd, F_q×=R×⟨−1⟩; χ therefore has a unique extension χ̃ to F_q× with χ̃(−1)=1. The full Gauss sum G(χ̃)=Σ_{x≠0}χ̃(x)ζ^x is Aχ+Bχ=0, a contradiction.

For completeness, its nonvanishing here is elementary. With χ̃ nontrivial, expand G(χ̃)G(χ̃⁻¹), substitute x=ty, and use Σ_{y≠0}ζ^{(t+1)y}=q−1 if t=−1 and −1 otherwise. The nontrivial character sum Σ_tχ̃(t)=0 then yields

    G(χ̃)G(χ̃⁻¹)=χ̃(−1)q=q=1 in Ebar.

Thus neither factor vanishes. For example, q=67 has m=11 and ord₁₁(3)=5, so its minor is nonsingular by this proof; ord₆₇(3)=22 gives loops of order 3⁷³⁸·67² under the preceding construction. The proof does not settle even-order Frobenius orbits or assert infinitely many qualifying primes. The scoped independent reviews below cover this continuation.

## Independent review of the conditional family

At exact source `7171a4e11376839d09b2a76544fed0c941b2507e`, GPT-6.1 Terra reviewers [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the conditional prime-family theorem and exact within-family isomorphism relation. Both checked the quadratic-character correlation, Gaussian periods, support equations and forbidden-line count, actual stabilizer real-class exclusion, full folder and strict-defect arguments, elementary Moufang primitivity obstruction, complement/automorphism necessity and sufficiency, and Burnside formula. Both read the exact certificate and independently ran it: the S₅ reviewer extracted the pinned file and used bundled Python 3.12 (about 0.3 s); the presentations reviewer used Python 3.12.14. All q=7 and q=19 minor, period, support and count assertions passed. Their acceptance retains the explicit minor hypothesis and cited prior interfaces, and does not cover the later group-algebra or nonvanishing extensions. No global classification, infinitude, novelty or formal verification was certified.

At exact source `123933cc594b601dd317d62b333a949d20431d35`, the same two reviewers independently accepted the group-algebra criterion and both sufficient nonvanishing corollaries. They checked the convolution indexing, unit/gcd criterion, characteristic-three multiplicities, local group-algebra case, odd-Frobenius exchange of the two half-sums and the elementary Gauss-product contradiction. Both independently checked the q=67 arithmetic. This extends the analytic prime subclasses but does not prove general nonvanishing, necessity of the sufficient criterion or infinitude. No new finite-field computation or formal verification was claimed for this proof.

## Jacobi-sum obstruction and necessity for the displayed support

**Independently reviewed continuation of the group-algebra and odd-Frobenius results at exact reviewed source `123933cc594b601dd317d62b333a949d20431d35`.** For a nontrivial prime-to-three character χ of R, extend it uniquely to F_q× by χ(−1)=1, and let η be the quadratic character. Extend both characters by 0 at 0. Define, in an algebraic closure of F₃,

    Gψ=Σ_{x≠0}ψ(x)ζ^x,       Jχ=Σ_x χ(x)η(1−x).           (14)

The Fourier minor M is singular if and only if some such χ satisfies

    Jχ²=−1.                                                (15)

This is an exact criterion involving only the finite field generated by the character values. To prove it, write Aχ=Σ_{r∈R}χ(r)ζ^r and Bχ=Σ_{r∈R}χ(r)ζ^{−r}. Since −1∈N and χ(−1)=1,

    Gχ=Aχ+Bχ,       Gχη=Aχ−Bχ.

The elementary Gauss–Jacobi identity GχGη=JχGχη shows that Bχ=0 exactly when Jχ=Gη. Here Gχη≠0 and Gη²=η(−1)q=−1 in characteristic 3. For completeness, group x+y=t in GχGη: the t=0 term vanishes because χη is nontrivial, and for t≠0 substitute x=tu, y=t(1−u). The Gauss product GψGψ⁻¹=ψ(−1)q follows by substituting x=ty and evaluating the inner additive sum; it gives

    Jχ J_{χ⁻¹}=q=1.                                        (16)

If the minor is singular, the reviewed group-algebra criterion gives Bχ=0 for some χ; the trivial character cannot occur because the period t is nonzero. Thus (15) follows. Conversely, (15) gives Jχ=±Gη. If the sign is positive, Bχ=0. If it is negative, (16) and Gη²=−1 give J_{χ⁻¹}=Gη, so Bχ⁻¹=0. The group-algebra criterion then makes M singular. This establishes (15) without assuming that 3 is primitive modulo q or invoking characteristic-zero Fourier-minor results.

There is a further nonvanishing criterion for some even Frobenius orbits. If χ has order ℓ and an **even** positive e satisfies 3^e≡−1 mod ℓ, then Bχ≠0. Otherwise Jχ=Gη; Frobenius^e sends χ to χ⁻¹, fixes η and fixes Gη∈F₉, so J_{χ⁻¹}=Gη as well. Equation (16) would give 1=Gη²=−1. In particular this covers prime-power ℓ when ord_ℓ(3) is divisible by 4, because the unique order-two element modulo an odd prime power is −1. For composite ℓ, divisibility of ord_ℓ(3) by 4 alone is not asserted to imply the required inversion. For example, the nontrivial prime-to-three characters for q=31 have order 5, so this argument proves the base minor nonsingular there. Combined with the reviewed odd-Frobenius theorem, it supplies further sufficient cases; it is not a universal nonvanishing theorem.

**A counterexample to universal nonsingularity.** Take q=2311, so q≡7 mod 12 and q−1=2·3·5·7·11. The [standalone exact certificate](../code/verify_odd_heisenberg_jacobi_obstruction.py) checks q is prime and 3 generates F_q×. Let ω be a primitive seventh root in F₃[ω]/(1+ω+⋯+ω⁶)=F_{3⁶}, and choose χ(3)=ω⁴. Then χ has order 7 and χ(−1)=1. The certificate obtains the signed Jacobi-sum coefficient counts

    (17,−12,−12,−20,18,22,−14),

and verifies in F_{3⁶} that

    Jχ=1+2ω+2ω²+2ω⁴,       Jχ²=−1.

Hence (15) proves M singular for q=2311. The field used is genuine because ord₇(3)=6; the check does not construct a field containing a primitive 2311st root. This counterexample does not affect the conditional construction for primes satisfying (1).

The minor condition is also **necessary for a folder with the exact support W in (3)**. If M is singular, choose a nonzero column vector c=(c_r)_{r∈R} in its kernel. The sum of all rows of M is the constant row t(1,…,1): for each r∈R, multiplication by r permutes N. Since st=−1, t≠0, and therefore Σ_r c_r=0. Put h=Σ_{r∈R}bar(c_r)e_r. The N-coordinates of σh are Mc=0, while its 0-coordinate is Σ_r c_r=0; hence h and σh both lie in

    V_R=⊕_{r∈R}E e_r.

Thus V_R∩σ(V_R) is a nonzero E-subspace stable under the F₀-semilinear involution σ. Semilinear descent supplies a nonzero σ-negative vector in this intersection. Every displayed W contains V_R, so H contains a nonidentity τ-inverted element and K cannot be a transversal to H. Consequently, for each prime q≡7 mod 12, nonsingularity of M is equivalent to existence of a folder with the displayed R-support and the allowed-line choices (3). At q=2311 no choices of U and b in this displayed support give a folder. This says nothing about other Heisenberg stabilizers or other constructions at that prime.

The criterion, even-Frobenius improvement, q=2311 obstruction, and converse in this section have the independent exact-source reviews below. The certificate is finite arithmetic evidence, not a substitute for that review.

At exact source `ceb13792291dc825dc9dc4f1cfeaf6a190deba6e`, GPT-6.1 Terra reviewers [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the Jacobi criterion, even-Frobenius deduction, q=2311 obstruction and necessity for the displayed full-R support, conditional on the reviewed prior family/group-algebra inputs. Both checked the Gauss–Jacobi signs and inverse-character case, the actual σ-stable kernel subspace, and its negative vector. Both read and independently ran the committed certificate: the S₅ reviewer used bundled Python 3.12 (about 0.1 s), the presentations reviewer Python 3.12.14. All primality, primitive-root, character-field and Jacobi-square assertions passed. This is an exact admissibility test for the displayed family; neither review excludes other stabilizers at q=2311 or asserts global classification, novelty or formal verification.
