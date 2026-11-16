# Classification of extraspecial-derived odd Bol loops

**Continuation of 0323:C0010 [context outside this selected packet: `../claims/C0010.md`], with the scoped independent reviews below.** Let \(Q\) be a finite simple nonassociative odd-order left Bol loop with canonical faithful generating folder \((G,H,K)\) and canonical inversion \(\tau\). Suppose \(D=G'\) is nilpotent and each nontrivial Sylow factor \(P_p\) of \(D\) is extraspecial. Put \(A=G/D\). Conditional on the reviewed source inputs below, the necessary conclusion is
\[A\cong\prod_{p\mid |D|}C_p,\qquad H\cap C_G(\tau)=1,\qquad |H|=|Q|.\tag{1}\]
In particular \(A\) is cyclic of squarefree order. This first part proves the necessary structure; the subsequent sections give the restricted classification. The reviewed arbitrary-principal-isotope interface then also gives the G-loop property, as explained below.

Use [the nilpotent-derived restrictions](odd-nilpotent-derived.md#extraspecial-sylow-factors-exponent-and-module-restrictions), “Extraspecial Sylow factors,” independently accepted at `6033272fbbd42f39c07ae59808ca122c9d60348e`, and the odd-envelope derived and marked-class inputs reviewed at `e896039d004ff3882621aca115b1a39cc8fed207`. In particular \(G=HD\), \(C_G(\tau)\le D\), \(|H|=|C_G(\tau)|\), and \(H\cap\Lambda^2=1\) for \(\Lambda=\widehat\tau K\), the full outside-involution class in \(G\rtimes\langle\widehat\tau\rangle\). For each \(p\), \(Z_p=Z(P_p)\le Z(G)\) has order \(p\), \(U=P_p/Z_p\) is an \(\mathbb F_p A\)-module with a nondegenerate alternating form, \(U^{A_{p'}}=0\), and the shadow \(W=(H\cap P_p)Z_p/Z_p\) is \(A\)-invariant and isotropic. Also \(W\cap\tau(W)=0\), and \((H\cap\tau H)\cap P_p=1\).

## Splitting and simultaneous local alignment

Fix \(p\mid |D|\). Write \(D_{p'}=\prod_{r\ne p}P_r\), \(B=A_{p'}\) and \(R=A_p\). Form
\[\overline G=G/(Z_pD_{p'}),\quad 1\to U\to\overline G\to A\to1.\]
Adjoin the formal inversion involution to obtain \(\overline G^+=\overline G\rtimes\langle\widehat\tau\rangle\), an extension of \(\Gamma=A\rtimes\langle\widehat\tau\rangle\) by \(U\). The normal subgroup \(B\triangleleft\Gamma\) has order prime to \(p\), and \(U^B=0\). The following elementary complement argument supplies the needed splitting and conjugacy, without an unproved extension-splitting assumption. For any extension E of Γ by U, the inverse image of B has a complement B₀ to its normal Hall subgroup U, by Schur–Zassenhaus. All such B-complements are U-conjugate. As B is normal in Γ, conjugation by every element of E sends B₀ to one of these complements, so E=U N_E(B₀). But U∩N_E(B₀)=C_U(B₀)=U^B=0: a normalizer element in U has commutators with B₀ in U∩B₀. Thus N_E(B₀) maps isomorphically onto Γ and is a complement. Any Γ-complement contains a B-complement and normalizes it, so the same argument makes all Γ-complements U-conjugate. The Schur–Zassenhaus input is [Craven, 2012, §2.1, Theorem 2.1](../REFERENCES.md); its soluble-kernel or soluble-quotient condition holds in every application here. The existing formal involution has order two, as does the involution in a complement; their images in \(\Gamma\) agree and Schur–Zassenhaus conjugacy in \(U\rtimes C_2\) moves one to the other by \(U\). Hence a \(\Gamma\)-complement can be chosen to contain the original \(\widehat\tau\). Its \(A\)-part \(A_0\le\overline G\) satisfies \(\tau(a)=a^{-1}\) for \(a\in A_0\).

The image \(\overline H\) intersects \(U\) in precisely \(W\): if a representative of an element of \(H\) lies in \(P_p Z_pD_{p'}=D\), then \(H\cap D\) splits by Sylow primes. The quotient \(\overline H/W\) is a complement to \(U/W\) over \(A\). As \(W\) is \(A\)-invariant and \(B\) has order prime to \(p\), fixed points are exact, so \((U/W)^B=0\). Applying the preceding complement-conjugacy argument with kernel U/W and quotient A makes its A-complements conjugate by U/W. Conjugating \(H\) by a suitable element of \(P_p\), while retaining the fixed \(A_0\) and \(\widehat\tau\), arranges
\[\overline H=W\rtimes A_0.\tag{3}\]
This replacement is legitimate because every conjugate of \(H\) still has trivial intersection with \(\Lambda^2\); it need not be fixed by \(\tau\). No complement to \(D\) in \(G\) has been assumed.

Let \(H_p\in\operatorname{Syl}_p(H)\). Its image in \(\overline H\) is a Sylow subgroup \(W\rtimes R\), and the map is injective: its kernel is a \(p\)-subgroup of \(H\cap Z_pD_{p'}\), but \(H\cap Z_p=1\) by core-freeness and \(D_{p'}\) has order prime to \(p\). Thus \(H_p\cong W\rtimes R\). Let \(C\le H_p\) be the inverse image of the pure \(R\)-subgroup in (3); then \(C\cong R\), and \(C\cap D_{p'}=1\).

## Central character and marked collision

In \(\widetilde G=G/D_{p'}\), the images of \(C\) and its inversion by \(\tau\) have the same pure-\(R\) image in \(\overline G\). Thus for each \(c\in C\),
\[\tau(c)c\in Z_p\quad\text{in }\widetilde G.\]
Since \(C\) is abelian and \(Z_p\) is central, this defines a homomorphism \(\chi:C\to Z_p\). Let \(C_0=\ker\chi\). Its preimage \(C_0D_{p'}\) is \(\tau\)-stable, and \(C_0,\tau(C_0)\) are complements to its normal Hall \(p'\)-subgroup \(D_{p'}\). Schur–Zassenhaus conjugacy supplies \(d\in D_{p'}\) such that an outside element \(d\widehat\tau\) normalizes \(C_0\). It induces inversion on \(C_0\), because it does so modulo \(D_{p'}\) and \(C_0\cap D_{p'}=1\). An odd power of \(d\widehat\tau\) is an outside involution \(\lambda\) with the same inversion action. As \(|G|\) is odd, all outside involutions are conjugate to \(\widehat\tau\), hence lie in \(\Lambda\).

For \(c\in C_0\), \(c^{-1}c^\lambda=c^{-2}\) lies in the conjugate of \(H\) containing \(C_0\) and in \(\Lambda^2\). The latter follows as a product of \(\lambda\) and its \(c\)-conjugate. Marked transversality gives \(c^{-2}=1\), and oddness gives \(c=1\). Thus \(\chi\) is injective and
\[|A_p|=|C|\le |Z_p|=p.\tag{4}\]
The reviewed no-normal-Hall consequence gives \(p\mid |A|\), since \(P_p\) is proper normal; hence \(|A_p|=p\). This holds for every \(p\mid |D|\). Conversely every prime of \(A\) divides \(|D|\), because \(G=HD\), \(|H|=|C_G(\tau)|\), and \(C_G(\tau)\le D\). This proves the first equality in (1).

## Fixed dimensions and numerical consequences

Return now to the original stabilizer H. The temporary conjugation was used only to prove the invariant bound on |A_p|; the following shadow and fixed-stabilizer conclusions apply to the original canonical folder.

The \(p'\)-group \(B\) acts semisimply on \(U\) without fixed vectors. Over an algebraic closure its nontrivial characters occur in distinct inverse pairs because \(|B|\) is odd; the symplectic involution interchanges their weight spaces, since it inverts \(A\). Hence
\[\dim C_U(\tau)=\tfrac12\dim U.\tag{5}\]
This does not require semisimplicity for the \(p\)-part of \(A\). Since \(Z_p\) is fixed and fixed-point lifting is coprime, \(|C_{P_p}(\tau)|=p^{1+\dim U/2}\). Also \(|H\cap P_p|=p^{\dim W}\). Comparing \(|H|=|A|\,|H\cap D|\) with \(|C_G(\tau)|=\prod_p|C_{P_p}(\tau)|\) prime by prime and using \(|A_p|=p\) yields \(\dim W=\dim U/2\). Thus each \(W\) is a maximal isotropic (Lagrangian) subspace. The reviewed equality H∩τ(H)=H∩C_G(τ), together with C_G(τ)≤D and (H∩τ(H))∩P_p=1 for each p, gives H∩C_G(τ)=H∩τ(H)=1. Here a subgroup of nilpotent D splits into its Sylow subgroups, so the trivial intersections with every P_p suffice. Finally the same prime-power counts give \(|H|=|Q|\).

The equalities also give the G-loop property using the reviewed arbitrary-principal-isotope interface at `ea836a5f328d6bc52913aac8fd1841a87072f5f8`, exactly as in `odd-cross-graph-family.md`: \(H\cap C_G(\tau)=1\) makes the \(H\)-action on \(\Lambda=\widehat\tau^G\) free at \(\widehat\tau\), and \(|H|=|Q|=|\Lambda|\) makes its orbit all of \(\Lambda\). For each \(k\in K\), some \(h\in H\) conjugates \(\widehat\tau\) to \(\widehat\tau k\); the same conjugation identifies \(K\) with \(k^{-1}K\). The cited isotope interface then makes \(Q\) isomorphic to every principal isotope, and hence a G-loop. This uses that interface as an input and requires independent review of the present application.

## Evidence and remaining obligation

The bounded endpoint above is the necessary squarefree abelianization and Lagrangian-stabilizer theorem under the all-extraspecial hypothesis. The baseline previously supplied only exponent, composition-factor and shadow-avoidance constraints. The necessity argument alone does not classify group extensions, module actions or stabilizers. The new continuation below addresses that gap through a simultaneous normal form and a construction/isomorphism theorem; neither scalar graph actions nor semisimplicity of the own-prime action is assumed necessary.

The necessity theorem has the exact-source reviews recorded next; they do not cover the later classification continuation. No computation, literature novelty or formal verification is asserted. The invoked strict-defect and isotope interfaces retain their recorded qualifications; this is not a complete classification of finite simple Bol loops.

## Independent review of the necessity theorem

At exact source `7941d518a3142819b44a75b089c1386b206e87f1`, GPT-6.1 Terra reviewers [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the necessity theorem above. Both checked the elementary complement lemma, alignment while retaining the original involution, the injective Sylow lift, the central-character kernel collision, restoration of the original stabilizer, weight-space dimension count and regularity/G-loop deduction. Their acceptances retain the cited extraspecial restrictions, marked/strict-defect inputs, Schur–Zassenhaus and principal-isotope interface. Neither used a computation, claimed formal verification or reviewed the following new classification continuation.

## Classification endpoint and precise construction data

**Continuation with the scoped independent reviews below.** The endpoint here is a complete construction and isomorphism classification of finite simple nonassociative odd left Bol loops whose canonical left multiplication group G has nilpotent derived subgroup D and every nontrivial Sylow subgroup of D extraspecial. This is a restricted structural branch of 0323.CLASSIFY. The baseline is the necessary squarefree abelianization/Lagrangian theorem just reviewed, together with the constructed scalar graph family. The gap addressed below is exhaustion of all extensions, actions and stabilizers in this branch, including reducible and own-prime unipotent actions. Other nilpotent-derived groups, nonnilpotent derived groups and even loops remain outside the hypotheses.

Take a finite set I of at least two pairwise distinct odd primes p_i, and a labeled squarefree cyclic group A=∏_i⟨b_i⟩, |b_i|=p_i. For each i take a nonzero finite-dimensional F_{p_i}-space W_i with a nondegenerate alternating form β_i, and a representation

    R_i:A→GL(W_i)

such that every R_i(a) is β_i-self-adjoint and W_i^{B_i}=0, where B_i=∏_{j≠i}⟨b_j⟩. The commuting operators need not be scalar or semisimple. Define the cross-action graph by j→i for j≠i precisely when R_i(b_j)≠1. Require this graph to be strongly connected. This ensures that the combined A-action is faithful, since every prime-order coordinate has an outgoing edge and a kernel in squarefree A is a product of coordinate subgroups.

On ∏_i(W_i×F_{p_i}) put

    (u,a)·(v,b)
      = (u_i+R_i(a)v_i, a_i+b_i−β_i(u_i,v_i))_i,       (6)

where a denotes the element ∏_j b_j^{a_j} of A. The assertions proved in the continuation are:

1. These data give a simple proper odd left Bol G-loop of order ∏_i p_i^{dim W_i+1}, with nilpotent derived canonical group and all its Sylow factors extraspecial.
2. Every loop in the stated structural branch is isomorphic to one of (6).
3. Two such data give isomorphic loops exactly when they have the same primes and there are v_i∈F_{p_i}× and F_{p_i}-linear bijections T_i:W_i→W_i′ satisfying

       β_i′(T_i x,T_i y)=v_i β_i(x,y),
       T_i R_i(b_j)=R_i′(b_j′)^{v_j} T_i  for every i,j. (7)

The final section converts these operator data into character-orbit partitions and a finite explicit equivalence relation; thus (7) is not an instruction to enumerate arbitrary groups or loops.

## Global splitting and preservation of the original loop

Write Z=Z(D)=∏_iZ_i, U=D/Z=⊕_iU_i and W=⊕_iW_i, with the necessity theorem's notation. For each i its elementary complement lemma applies to the extension of Γ=A⋊⟨τ̂⟩ by U_i, because the normal coprime B_i fixes no vector. These separate extensions split simultaneously: the extension by U is the fiber product over Γ of its quotients by ⊕_{j≠i}U_j. The map to that fiber product is injective with equal finite orders. Choose the local complements to contain the existing τ̂; their fiber product does too. Thus

    (G/Z)⋊⟨τ̂⟩=(U⋊A₀)⋊⟨τ̂⟩,

where τ inverts A₀. The same elementary complement-conjugacy argument applies componentwise to U_i/W_i, since coprime fixed points are exact and (U_i/W_i)^{B_i}=0. Conjugating H by an element of D therefore arranges HZ/Z=W⋊A₀.

This last adjustment preserves the loop up to an actual folder isomorphism, not just transversality. The necessity theorem gives H∩C_G(τ)=1 and |H|=|C_G(τ)|=|Q|, hence G=C_G(τ)H. If the required adjustment is H′=gHg⁻¹, write g=ch with c∈C_G(τ), h∈H. Then H′=cHc⁻¹, and c also preserves τ and its full inverted set K. Conjugation by c is consequently an isomorphism (G,H,K)→(G,H′,K). Continue with the aligned H.

Let E be the inverse image of A₀ in G. It is a central extension by Z. The actual subgroup C=E∩H maps onto A₀, with kernel H∩Z=1, so E=Z×C, C≅A and

    G=D⋊C,    H=(H∩D)⋊C.

For c∈C, χ(c)=τ(c)c∈Z is a homomorphism. Its restriction C_i→Z_i is injective by the necessity theorem's marked collision, now also directly because χ(c)=1 would put a nonidentity element of H in K. Thus χ:C→Z is an isomorphism. For a generator c_i of C_i set z_i=χ(c_i)^{1/2} and b_i=c_i z_i⁻¹, using the unique square root in odd Z_i. Then τ(b_i)=b_i⁻¹, the b_i commute, and

    G=D⋊A,    H=(∏_iS_i)⋊⟨b_i z_i:i∈I⟩,             (8)

where S_i=H∩P_i. These are actual complements and stabilizers, with no residual extension cocycle.

Each U_i=W_i⊕τ(W_i). If ω_i is its central commutator form, define β_i(x,y)=ω_i(x,τ y) on W_i. This is nondegenerate alternating because both halves are complementary Lagrangians and τ is symplectic. The A-action R_i on W_i is β_i-self-adjoint: symplectic invariance and τaτ=a⁻¹ give β_i(R_i(a)x,y)=β_i(x,R_i(a)y). Also W_i^{B_i}=0. The actual S_i and τ(S_i) are complementary isotropic lifts, and class-two exponent-p_i coordinates identify P_i with

    (W_i⊕W_i)×F_{p_i},
    (x,y,z)(x′,y′,z′)
      =(x+x′,y+y′,z+z′+½[β_i(x,y′)+β_i(y,x′)]),
    τ(x,y,z)=(y,x,z),
    a(x,y,z)=(R_i(a)x,R_i(a)⁻¹y,z).                    (9)

To see there is no omitted central shear, C normalizes S_i; since τ(c)=c⁻¹χ(c) with χ(c) central, it also normalizes τ(S_i). In coordinates based on these actual subgroups, both coordinate axes have zero central component under C. The action fixes Z_i and is therefore exactly the displayed linear action. This completes necessity of the operator normal form before simplicity is imposed.

## Construction, transversality and canonical group

Conversely begin with the operator data, temporarily requiring only faithful combined action rather than strong connectivity. Form the extraspecial exponent-p_i groups (9), their product D and G=D⋊A; define τ, H by (8)–(9). Self-adjointness makes the action symplectic and τ an automorphism. The twisted generators b_i z_i commute and have order p_i. Put K={g∈G:τ(g)=g⁻¹}. Over torus label a, every element of K has local coordinates

    k_i(x,a)=(x,−R_i(a)⁻¹x,0).                        (10)

These equations follow by comparing τ(g) and g⁻¹; the odd central coordinate satisfies 2z=0. If k(x,a)k(x′,b) lies in H, its second vector coordinate is zero, forcing x′=−R_i(b)x at each i. The first coordinate is (1−R_i(ab))x and its central coordinate is

    ½[β_i(x,R_i(a)⁻¹x)+β_i(x,R_i(b)x)]=0.

For any self-adjoint operator R in odd characteristic, alternation gives β_i(x,Rx)=−β_i(x,Rx), hence zero. But an H element above ab has central coordinate equal to the b_i exponent of ab. All these coordinates vanish only when ab=1, and then the first vector coordinates vanish too. Thus H∩K²=1.

In the odd group G⋊⟨τ̂⟩, Schur–Zassenhaus makes all outside involutions one conjugacy class Λ=τ̂K. Hence Λ²=K² is G-conjugacy invariant, so the same trivial intersection holds for every conjugate of H. Equation (10) gives

    |K|=|A|∏_i|W_i|=[G:H],
    |H|=|C_G(τ)|=∏_i p_i|W_i|,   |G|=|H|².

The inverse- and sandwich-closed full inverted set is therefore a transversal to every conjugate of H and gives a left Bol loop by the pinned folder correspondence.

Coprime averaging gives [U_i,B_i]=U_i. Commutators with A thus generate P_i/Z_i and then P_i, since Z_i=Φ(P_i). Consequently G′=D. Moreover A⊂K, and in odd G the full inverted set is the set of τ-commutators; its generated subgroup is normal. The same commutator calculation proves ⟨K⟩=G. If a normal subgroup of G lies in H, its intersection with D splits over the distinct Sylow primes and must be trivial: every nontrivial normal subgroup of P_i meets its prime-order center, disjoint from H. It then centralizes D. Faithful A-action gives C_G(D)=Z(D), also disjoint from H, so the subgroup is trivial. Thus G is the faithful canonical left multiplication group. Conversely a nontrivial kernel coordinate in A would give a nonidentity central twisted generator in H, so faithfulness is necessary here.

Finally H∩C_G(τ)=1, since fixedness kills the odd torus labels and τ exchanges the vector halves. The displayed sizes make H regular on Λ. The already reviewed principal-isotope interface therefore gives the G-loop property as in the necessity theorem.

## Simplicity exactly when the cross-action graph is strongly connected

Let N◁G be τ-stable, L=N∩D=∏_iL_i, and I_N the support of its image in squarefree A. If L_i≠1, then Z_i≤L_i. Write V_i=L_i/Z_i, c_i=dim(V_i)₊ and w_i=dim(V_i∩W_i). Projection along (V_i)₋ is injective on V_i∩W_i because τ swaps the two coordinate halves. Hence w_i≤c_i and

    |C_{L_i}(τ)|/|S_i∩L_i|=p_i^{1+c_i−w_i}≥p_i.       (11)

For L_i=1 the ratio is one. If j∈I_N and j→i, commutators of a lift of b_j with P_i are nonzero modulo Z_i, so L_i≠1. This implication does not require a scalar action or assert L_i=P_i.

Let J be the image of H∩N in A. If i belongs to its support, isolate the p_i-primary part of an element of H∩N with nonzero i-coordinate; its only torus label is a nonzero power of b_i. If this acts nontrivially on U_i, its commutators already force L_i≠1. If the action on U_i is trivial but its S_i-coordinate is nonzero, commutators with P_i force Z_i≤L_i. If both are trivial, its product with its τ-image lies in N∩D and has P_i-coordinate a nonzero power z_i^{2k}. Taking the p_i-primary component in the nilpotent subgroup N∩D puts that central element in L_i. Therefore every support coordinate of J has L_i≠1.

Since τ inverts odd A, C_N(τ)=∏_iC_{L_i}(τ), while the kernel of H∩N→J is ∏_i(S_i∩L_i). Each J-coordinate cancels at most the single p_i factor furnished by (11). If I_N is empty and N≠1, the defect is strict. If I_N is nonempty and proper and the graph is strongly connected, there is an edge leaving I_N; its target contributes an uncancelled prime outside supp J. If I_N is all I, commutators with lifts of B_i have image [U_i,B_i]=U_i for every i, so the Frattini property gives P_i≤N for all i and N=G. Thus every proper nontrivial τ-stable N has strict defect. The exact criterion reviewed at `65a3e58df517df59656ab948ac9d122208f62c4a` gives simplicity, retaining its maximal-simple-quotient argument rather than assuming inversion descends to every quotient.

Conversely a graph that is not strongly connected has a nonempty proper sink vertex set I₀. Then

    N₀=(∏_{i∈I₀}P_i)⋊∏_{i∈I₀}⟨b_i⟩

is normal and τ-stable: no included torus coordinate acts on an omitted P_j. Its fixed and H-intersection orders both equal ∏_{i∈I₀}p_i|W_i|. Equality in the reviewed defect formula gives a quotient folder. It is proper and nontrivial: HN₀<G because an omitted P_j is not covered, and K∩N₀ contains nonzero τ-negative vectors in an included factor. This proves nonsimplicity and the criterion in both directions.

## Coordinates and direct properness

Use right-H coset representatives (0,u_i,a_i)_i in D. The unique K representative has torus label −a and local vectors (−R_i(−a)u_i,u_i), with zero center. For the product of two such section elements, set c=a+b. Before normalization the local vectors and center are

    x=−R_i(−a)u_i−R_i(−c)v_i,   y=u_i+R_i(a)v_i,
    z=−½[β_i(u_i,v_i)+β_i(u_i,R_i(−c)v_i)].

Right multiplication by the inverse torus label in H adds c_i to the center. The following S_i translation killing x adds

    −½β_i(y,x)=½[β_i(u_i,R_i(−c)v_i)−β_i(u_i,v_i)].

Their sum is c_i−β_i(u_i,v_i), proving (6), including all own-prime actions.

For any edge j→i choose u with (R_i(b_j)−1)u≠0, and v with β_i((R_i(b_j)−1)u,v)≠0. Take x with only central coordinate a_j=1, and y,z with only node-i vectors u,v. In (xy)(zx) and (x(yz))x all coordinates agree except the node-i central coordinates, respectively

    −β_i(R_i(b_j)u,v),    −β_i(u,v).

The central labels created during the products do not affect this calculation: x has zero vectors and i≠j. This is a direct Moufang-identity failure. Strong connectivity on at least two vertices ensures such an edge. No finite simple Moufang classification is used.

## Complete operator isomorphism criterion

A loop isomorphism identifies its canonical faithful generating folders, hence G′=D, the distinct Sylow P_i, their centers and S_i=H∩P_i. It preserves τ because that automorphism is uniquely determined by inversion on the generating K. Faithfulness gives Z(G)=Z(D). In the normalized folder the complement C=⟨b_i z_i⟩ has the intrinsic description

    C={h∈H:τ(h)h∈Z(G)}.                              (12)

Indeed for h=s c with s∈∏S_i, its τ(h)h image in each U_i has one component in τW_i coming from τs_i and one in W_i from c_i⁻¹s_i c_i. It is zero precisely when every s_i=1. Thus an isomorphism takes the generator c_i=b_i z_i to c_i′^{v_i}. Since τ(c_i)c_i=z_i², it takes z_i to z_i′^{v_i}, and b_i=c_i z_i⁻¹ to b_i′^{v_i}. Its induced map on W_i consequently has the multiplier v_i and intertwining equations (7). This proves necessity without an unspecified complement cocycle.

Conversely (7) defines the map (x,y,z)↦(T_i x,T_i y,v_i z) on P_i and b_i↦b_i′^{v_i}. Equation (9) makes it a group isomorphism commuting with τ and carrying S_i and b_i z_i to their primed counterparts. It therefore carries H,K to H′,K′ and gives a loop isomorphism. Different prime sets cannot be identified because D and its Sylow factors are characteristic. This proves the complete criterion (7).

## Character and partition parameters

The operator description has an explicit discrete normal form. Fix i, put p=p_i and B=B_i. A nontrivial irreducible F_p-character of cyclic B is a Frobenius orbit ξ of linear characters over an algebraic closure; its image algebra is E_ξ=F_{p^{r_ξ}}, where r_ξ is the degree of that orbit. For each such ξ and each integer k with 1≤k≤p, choose a nonnegative integer n_{i,ξ,k}. At least one n must be nonzero for each i. This means 2n_{i,ξ,k} Jordan blocks of length k for the own-prime operator R_i(b_i)−1 on the ξ-component. The dimension is

    dim_Fp W_i=∑_{ξ≠1} r_ξ∑_{k=1}^p 2k n_{i,ξ,k}.    (13)

These are all the parameters for fixed labeled A. In particular every Jordan block size must occur with even multiplicity; there are no additional form discriminants or extension parameters.

Here is an elementary proof. Since B has coprime order, its action is semisimple. Its isotypic idempotents are polynomials in commuting self-adjoint operators, hence are self-adjoint, so distinct components are β-orthogonal. The trivial component is absent. On a ξ-component, every e∈E_ξ is self-adjoint. The nondegenerate trace pairing defines a unique E_ξ-bilinear form β_E by

    Tr_{E/Fp}(e β_E(x,y))=β_i(ex,y)  for all e∈E.

Self-adjointness gives bilinearity over E; alternation follows because β_i(ex,x)=−β_i(ex,x), and nondegeneracy follows from that of β_i. Thus β_E is symplectic. The operator T=R_i(b_i)−1 is E-linear, self-adjoint and satisfies T^p=0.

Choose a vector x of maximal Jordan length k and y with β_E(T^{k−1}x,y)≠0. Each cyclic span E[T]x and E[T]y is isotropic, since β_E(T^a x,T^b x)=β_E(x,T^{a+b}x)=0. The cross-pairing matrix has nonzero antidiagonal and vanishes when a+b≥k, so their direct sum is a nondegenerate 2k-space. Its orthogonal complement is T-stable. Iteration proves the paired Jordan multiplicities. Within a pair, replacing y by an invertible polynomial in T normalizes the cross-pairing to

    β_E(T^a x,T^b y)=1 if a+b=k−1, and 0 otherwise.

This follows successively from the nonzero last coefficient, or equivalently by inverting the cross-pairing unit in E[t]/(t^k). Hence the unique standard block is the hyperbolic pair (E[t]/t^k)² with that pairing. Orthogonal sums prove existence and completeness of the n_{i,ξ,k}, including nonsemisimple own-prime actions.

Changing generators by α:b_j↦b_j′^{v_j} pulls back the B_i-character orbits by α and replaces the own-prime T by (1+T)^{v_i}−1. This polynomial is T times a unit and preserves all Jordan block sizes. The integer data give the same loop exactly when a single collection of source units (v_j)_j makes their orbit-indexed multiplicities agree after these pullbacks at every i. Frobenius is already included in the character orbits. The required multiplier v_i in (7) adds no obstruction: on each standard hyperbolic pair, scaling one cyclic half by any λ∈F_p× and fixing the other commutes with the representation and multiplies β_i by λ. Thus an isometry intertwiner can always be adjusted to the specified multiplier.

The cross-action graph is read directly from the data: j→i iff a character orbit with nonzero n_{i,ξ,k} is nontrivial on b_j. The own-prime action is nontrivial iff a block length k>1 occurs, and does not add a cross-edge. Strong connectivity is the only remaining simplicity test in these parameters. For fixed prime set and dimensions the parameter list and the source-unit equivalence are finite and explicit. Varying the dimensions gives the unbounded families covered by this theorem; this is not a uniform bound on all finite simple Bol loops.

## Scope, example and verification of the continuation

For every two distinct odd primes p,q, choose E=F_{p^{ord_q(p)}}, F=F_{q^{ord_p(q)}}. On W_p=E⁴ with the trace of the standard alternating J₄, take T=[[0,1],[0,0]], N=diag(T,Tᵀ), R_p(b_p)=1+N and R_p(b_q)=ζI for a scalar ζ of order q. Here N²=0 and NᵀJ₄=J₄N. On W_q=F² take R_q(b_p)=ηI, |η|=p, and R_q(b_q)=1. The graph has both cross-edges and the construction is simple and proper by the preceding argument. Its nontrivial own-prime action on P_p/Z_p is intrinsic and distinguishes it from every member of the earlier scalar graph family. Its order is p^{4ord_q(p)+1}q^{2ord_p(q)+1}. This example explains why scalar-graph exhaustion would have failed even inside the extraspecial-derived branch.

The standalone [operator coordinate certificate](../code/verify_odd_extraspecial_operators.py) instantiates p=3,q=13 with F₂₇=F₃[t]/(t³−t+1), the encoded order-13 scalar 6, and the displayed nonzero square-zero N on F₂₇⁴. It implements BCH group multiplication and right-H normalization independently of (6). Root read its source and ran it with bundled Python 3.12.14 and assertions enabled: 104 section/identity controls and 500 fixed-seed group-coset/left-Bol comparisons passed; the explicit Moufang witness gives central values 10 and 12 modulo 13. These finite samples do not prove universal identities, simplicity, normal-form necessity or classification. No entire loop was enumerated.

At exact source `dce010e03e56d50af4fbfbb4aba69806228ec518`, GPT-6.1 Terra reviewers [model reviewer identity omitted], [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the complete classification continuation. All three checked the simultaneous splitting and actual-folder alignment, central character and absence of shears, full operator construction, both directions of the strong-connectivity criterion, direct properness, intrinsic complement, and complete operator and character-partition equivalence. Their acceptances conclude that the stated restricted branch endpoint is achieved under the cited inputs. Reviewer [model reviewer identity omitted] additionally read and accepted the full operator certificate and independently reran its pinned source with bundled Python 3.12 and assertions enabled, reproducing the stated controls and witness. The other two reviewers did not audit or run that optional certificate. These are independent model reviews, not formal verification. They depend on the accepted necessity theorem and its recorded interfaces, not on an assumption that all nilpotent-derived groups are extraspecial products. No claim of literature novelty or formal verification is made. This closes only the precisely stated extraspecial-derived branch under those dependencies, leaving the complete finite-simple-Bol classification open.
