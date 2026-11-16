# Natural SL₃ affine regular subgroups: cohomological data and center counterexample

Provisional bounded work for C0010 [context outside this selected packet: `../claims/C0010.md`] and C0004 [context outside this selected packet: `../claims/C0004.md`], following [root-graph parameters](nonbruck-root-graph-parameters.md). This note has the scoped independent reviews below and does not claim a compact closed count. The exact-isomorphism conclusion is conditional on the C0004 affine family and folder-isomorphism interfaces, with scoped review at the revisions recorded in the claim. Nothing here classifies all non-Bruck even loops or all loops of the same order.

Let q=p^f, V=Fq³ over Fp, A=SL₃(q), and X=V⋊A. Let U≤A be the upper unitriangular subgroup. Every regular subgroup Y≤X has order q³ and is a p-group; thus π(Y) is a p-subgroup of A and is conjugate into U by an element of A. Therefore it suffices to treat T:=π(Y)≤U, without assuming any property of the center of the Sylow group V⋊U.

## Exact regular-subgroup data

For each T≤U and each T-invariant Fp-subspace N≤V satisfying |T||N|=q³, form M=V/N. Consider maps ζ:T→M satisfying the cocycle equations

    ζ(st)=ζ(s)+s·ζ(t)   for all s,t∈T.                            (1)

They constitute the Fp-space Z¹(T,M), which is explicitly computable by linear equations from the multiplication and module-action data. Require also

    ζ(t)≠0 for every 1≠t∈T.                                      (2)

For such data define

    Y(T,N,ζ)={(v,t)∈V⋊T : v+N=ζ(t)}.                             (3)

Equation (1) makes (3) a subgroup, of order |N||T|=q³; equation (2) is equivalent to Y∩A=1, since A is the stabilizer of 0. Its orbit of 0 has size |Y| and is all V, so Y is regular. Conversely, for each Y with π(Y)=T and Y∩V=N, N is T-invariant and the unique coset v_t+N for elements (v_t,t)∈Y defines ζ. Closure gives (1), while regularity gives (2). Thus (T,N,ζ) are necessary and sufficient and uniquely reconstruct the subgroup Y after choosing the conjugate with T≤U.

A cocycle satisfying (2) is injective: ζ(s)=ζ(t) implies ζ(s⁻¹t)=s⁻¹(ζ(t)−ζ(s))=0. The prescribed cardinality makes it a bijection T→V/N as sets. Condition (2) is exactly the avoidance of the union of the linear evaluation kernels ker(ev_t) in Z¹(T,M), t≠1. It is not a list of loop multiplication tables; the residual classification is of unipotent subgroups, invariant subspaces, and vectors in explicitly presented linear cocycle spaces. No claim is made that these data are small or their orbit problem easy. T=1 gives N=V and Y=V, the translation case; exclude it for C0004's nontranslation simple-loop family.

## Explicit U₃ subgroup data

Write u(a,b,c)=[[1,a,b],[0,1,c],[0,0,1]], with

    u(a,b,c)u(a',b',c')=u(a+a', b+b'+a c', c+c').

For T≤U set B={b:u(0,b,0)∈T}≤(Fq,+), and let D≤Fq² be the image of T under u(a,b,c)↦(a,c). Then B,D are Fp-subspaces. The fibers above each d=(a,c) are b(d)+B for a unique function β:D→Fq/B, β(0)=0, satisfying

    β(d+d')=β(d)+β(d')+a c' + B.                                  (4)

Conversely every pair of subspaces B,D and function β satisfying (4) defines a subgroup T by these fibers; (4) includes all closure conditions, and finiteness gives inverses. Necessarily a c'−a' c∈B for d,d'∈D. Requiring β is essential: the commutator condition alone does not supply a solution to (4), especially in characteristic 2. Here |T|=|B||D|, so |N|=q³/(|B||D|). Once T and N are chosen, solving (1) is linear over Fp, and (2) is a finite hyperplane/subspace-avoidance condition. This yields explicit finite admissibility data for every q, albeit not a closed classification/count of possible triples.

### Explicit solution of the subgroup equation

Equation (4) also has a uniform solution test in each characteristic. Write $d=(a,c)$ and $d'=(a',c')$.

If $p$ is odd, solutions exist if and only if $ac'-a'c\in B$ for every $d,d'\in D$. Necessity follows by interchanging $d,d'$ in (4). For sufficiency, $B$ is an $\mathbb F_p$-subspace, so $1/2$ acts on $\mathbb F_q/B$, and

$$\beta_0(a,c)=\tfrac12 ac+B$$

satisfies (4): its polarization is $(ac'+a'c)/2$, congruent to $ac'$ modulo $B$. Every solution is $\beta_0+\ell$ for a unique $\mathbb F_p$-linear map $\ell:D\to\mathbb F_q/B$, since the difference of two solutions is additive.

If $p=2$, solutions exist if and only if $ac\in B$ for every $(a,c)\in D$. Necessity follows from setting $d'=d$ in (4). Polarizing this condition gives $ac'+a'c\in B$, making the bilinear map $D\times D\to\mathbb F_q/B$, $(d,d')\mapsto ac'+B$, alternating and symmetric. Choose an $\mathbb F_2$-basis $d_i=(a_i,c_i)$ of $D$ and define

$$\beta_0\!\left(\sum_i\epsilon_i d_i\right)
 =\sum_{i<j}\epsilon_i\epsilon_j a_i c_j+B,\qquad \epsilon_i\in\mathbb F_2.$$

Its polarization is $ac'+B$, using the diagonal vanishing and symmetry just proved, so it satisfies (4). Again every solution is $\beta_0+\ell$ for a unique $\mathbb F_2$-linear $\ell:D\to\mathbb F_q/B$. The choice of basis changes the displayed particular solution, not the complete solution set. Thus $B,D$ are admissible for some $\beta$ exactly under the respective conditions above; no hidden splitting hypothesis remains in this subgroup layer.

## Isomorphism interface

C0004 Theorem 2.1(3), under its exact stated hypotheses, makes isomorphism of loops from nontranslation regular Y equivalent to an automorphism of X preserving A and carrying Y to Y'. For A=SL₃(q), its action on V over Fp is faithful and irreducible; its centralizer algebra is Fq. Indeed, write a commuting Fp-linear map as a 3×3 block matrix of endomorphisms of Fq. Commutation with all elementary root matrices I+tE_ij for i≠j and t∈Fq forces its off-diagonal blocks to vanish and its diagonal blocks to be equal. The common block commutes with every multiplication-by-t map, hence is multiplication by its value at 1. Conversely scalar multiplications commute with A. Therefore N_GL3f(p)(A)=ΓL₃(q): any normalizer acts on the scalar centralizer as a field automorphism and then is Fq-linear; conversely ΓL₃(q) normalizes SL₃(q). The induced action on triples is

    g·(T,N,ζ)=(gTg⁻¹, gN, [gtg⁻¹↦gζ(t)]).

To work with the restricted representatives T≤U, declare two such triples equivalent when some g∈ΓL₃(q) maps one full triple to the other, even if g does not normalize the chosen U. This is a complete orbit relation conditional on C0004; quotient automorphisms/complement changes and factor swaps are handled by that cited theorem rather than assumed absent. C0004 applies for every q≥2 here because SL₃(q) is perfect with nonabelian simple projective quotient. Thus, conditional on C0004, every nontranslation triple constructs a finite simple proper left Bol loop of order q³|SL₃(q)|, and these orbits give its isomorphism data. Exact factorization gives τ(H)≠H when the two factors have distinct orders. For q=2, |A|=168>8; in general |A|=q³(q³−1)(q²−1)>q³, and q³|A|=q⁶(q³−1)(q²−1) is even. No closed orbit count or complexity bound is asserted.

## The SL₂ center-forcing proof fails for every even q

The Sylow group P=V⋊U is naturally UT₄(q). Its center is Z(P)=Fq e1. For q=2, use coordinates (v;U) with basis e1,e2,e3 and set

    a=(e3, I+E12),       c=(e1, I+E23).

These involutions generate Y0≅D8: b=(ac)²=(e1+e2,I+E13) has order two, is central in Y0, and [a,c]=b. Their eight elements have pairwise distinct translation components, so Y0 acts regularly on F2³; the projection Y0→U₃(2) is an isomorphism (equivalently its eight projected matrices are distinct). In particular Y0∩V=1, so Y0 does not contain Z(P).

For every q=2^f choose an F2-vector complement D with Fq=F2·1⊕D. The subgroup V_D=D³ of translations is invariant under U₃(2), since its matrix entries are in F2. Set Y=V_D⋊Y0. Its order is |D|³·8=q³, and it acts regularly on V=F2³⊕D³: Y0 first reaches the F2³ component of any vector and V_D supplies the remaining component. Moreover Y∩V=V_D, so

    Y∩Z(P)=D e1 < Fq e1=Z(P).

Thus the exact center saturation proved for SL₂ cannot extend to SL₃ as stated, already for every q=2^f≥4. The normalizer and construction arguments have the scoped reviews below; the explicit example can be independently checked by multiplying the two displayed affine generators.

## Independent review

GPT-6.1 Terra reviewers [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted this manuscript at exact source `0aef10b81068306fe6beb6f8a925fd9ecbfa9fc3`, conditional on the C0004 construction and isomorphism interface reviewed at `87a0895eec2cf7b690dafab5ca3292fb05147a03`. Both checked Sylow conjugation, the exact triple correspondence, the subgroup equations and their solutions in both characteristics, the full semilinear normalizer and orbit relation, and the explicit D₈ counterexample and extension to every even field. The result is effective algebraic data for this specified affine family, not a closed count or a census of all loops of its orders. No code or formal verification was used.
