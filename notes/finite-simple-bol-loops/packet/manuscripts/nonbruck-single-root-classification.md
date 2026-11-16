# Full single-root projection: center forcing and isomorphism data

**Continuation of 0323:C0010 [context outside this selected packet: `../claims/C0010.md`], using the scoped C0004 [context outside this selected packet: `../claims/C0004.md`] interface, with exact-source reviews recorded below.** Let q=p^f, d≥2, V=Fq^d over Fp, A=SL_d(q), and X=V⋊A. Put U={u(t)=I+tE12:t∈Fq}, W=Fq e1 and H={v:v₂=0}. It gives exact data and an equivalence relation for every regular Y≤X with 1≠π(Y)≤U. It makes no claim about subgroups whose linear projection is not conjugate into a single root group. Loop-isomorphism conclusions use C0004 and its hypotheses; for d=2, require q≥4.

## Root-image forcing

Let π(Y)=T={u(t):t∈S}, where 0≠S≤Fp Fq has dimension s. Put N=Y∩V. Regularity gives |Y|=|V| and |N|=q^d/|T|, so M=V/N has order |T|. The natural cosets ζ(t)=v+N for (v,u(t))∈Y form a bijective 1-cocycle ζ:T→M: it is a cocycle by closure and injective because Y∩A=1; cardinalities give surjectivity.

Write Z=(W+N)/N and D_t=u(t)−1 on M. This is well-defined because N is T-invariant. Every D_t annihilates Z, since u(t) fixes W pointwise. For each t≠0, im D_t=Z: on V, (u(t)−1)(x₁,x₂,...)=t x₂ e1, and as x₂ ranges over Fq its image is all W. Since T is abelian, the cocycle equation in the two orders gives

    D_t ζ(u)=D_u ζ(t)  for all t,u∈S.                         (1)

Suppose Z≠0. By surjectivity, choose t with ζ(t) a nonzero element of Z; then t≠0. Equation (1), together with D_u Z=0 for all u, says D_t annihilates every ζ(u), hence all of M. But im D_t=Z≠0, a contradiction. Therefore Z=0, equivalently

    W≤N.                                                       (2)

No assumption on p or s is needed. In particular the potential nontrivial unipotent action on M cannot occur for a regular subgroup in this single-root setting.

## Exact data and orbits

By (2), T acts trivially on M, so ζ is an Fp-linear bijection S→M. Let λ:V/W→S be the quotient map V/W→V/N followed by ζ⁻¹. Then λ is a surjective Fp-linear map and N/W=ker λ. Conversely, given any nonzero Fp-subspace S≤Fq and any surjective Fp-linear λ:V/W→S, let N/W=ker λ and define

    Y(S,λ)={(v,u(t)): λ(v+W)=t}.

This is a subgroup: u(t) acts trivially on V/W, so λ(v+u(t)w+W)=λ(v+W)+λ(w+W). It has |S||N|=|V| elements and intersects A trivially; hence it acts regularly on V. Its projection is exactly T_S, and the preceding construction recovers S,λ uniquely. Thus these are all regular Y with nontrivial projection contained in U.

For 0≠S,S'≤Fq, a semilinear map carrying Y(S,λ) to Y(S',λ') conjugates T_S to T_S'. All nonidentity u(t) have image W and fixed hyperplane H, so the map preserves the flag W⊂H. Consequently it has form g=Dσ, with σ a Frobenius field automorphism and

    D=[[a,b,c],[0,d0,0],[0,E,K]],  a,d0≠0, K∈GL_{d−2}(q),

where the block sizes are 1,1,d−2. Put k=a/d0. It sends u(t) to u(kσ(t)); hence the exact orbit relation is

    S'=kσ(S),    λ'(v+W)=kσ(λ(g⁻¹v+W))  for every v∈V.      (3)

Conversely every map of the displayed form satisfying (3) normalizes A and carries Y(S,λ) onto Y(S',λ'). This is a finite and explicit isomorphism relation on subspaces and surjective linear maps for every q,d; it does not supply a closed orbit count when dim S>1. A subgroup whose projection is conjugate into U can first be moved into U by GL_d(q), so the same data cover that entire conjugacy-invariant single-root projection family.

For d≥3, SL_d(q) is quasisimple, its natural Fp-module is irreducible and faithful, and N_GLdf(p)(SL_d(q))=ΓL_d(q), using the elementary-root scalar-centralizer argument in [the cocycle manuscript](nonbruck-affine-cocycle-data.md), reviewed at `0aef10b81068306fe6beb6f8a925fd9ecbfa9fc3`, and [the uniform prime-transvection theorem](nonbruck-prime-transvection-orbits.md), reviewed at `7530ae6eeeb0614d7c94ed6ab1f6761f3493ab88`. Thus, under C0004 Theorems 1.1 and 2.1(1)–(3), the data (S,λ) with S≠0 construct finite simple proper left Bol loops, and (3) is their exact loop-isomorphism criterion; each has order q^d|SL_d(q)|. For d=2 the same conclusion holds in the C0004 quasisimplicity range q≥4. The order-p transvection theorem separately solves the s=1 orbit space: two orbits for d≥3 and one for d=2. No inference is made for any loop outside these exact-factorization data.

The C0004 repair and specific folder/isomorphism application retain their scoped review at `87a0895eec2cf7b690dafab5ca3292fb05147a03`; this does not assert acceptance of C0004 in aggregate. The earlier cocycle/root-orbit inputs retain their separate exact-source review limits. The present proof requires no experimental evidence and has the separate mathematical reviews below.

## Grassmannian/projective normal form for fixed S

Fix an ordered Fp-basis s₁,…,s_s of S, and write λ=Σ_i s_i λ_i, where

    λ_i(y,z)=Tr_Fq/Fp(a_i y+Σ_{j=1}^{d−2} B_{ji} z_j).

Here z=(x₃,…,x_d), a=(a_i)∈Fq^s and B is a (d−2)×s matrix over Fq. Let R be the Fq-row space of B. Surjectivity of λ is equivalent to the coordinate functionals λ_i being Fp-linearly independent, which by nondegeneracy of the trace pairing is exactly

    (R+Fq a)^⊥ ∩ Fp^s = {0},                                  (4)

using the standard dot product on Fq^s. In particular dim_Fq R≤d−2.

First quotient by the subgroup of flag matrices with σ=id and k=a/d0=1. Such a matrix sends y to d0 y and z to Ey+Kz. Under its action, B is left-multiplied by an invertible (d−2)×(d−2) matrix, while a is replaced by d0⁻¹ times a plus an arbitrary row of R. Thus its complete invariant is

    (R, L),   L=0 or L=Fq(a+R)≤Fq^s/R.                       (5)

Indeed matrices of the same size and row space differ by an invertible row operation, including the rank-deficient case; the shear E gives every addition from R, and d0 independently rescales a by any nonzero field element. Conversely all three operations are realized by flag matrices with a=d0 and k=1. Every R with dim R≤d−2 and every zero or one-dimensional L satisfying (4) is realizable, by choosing B with rowspace R and a representative a of L. Condition (4) does not depend on the representative or nonzero scalar.

The remaining transformations are the finite maps induced on (5) by (3) with kσ(S)=S; they are well-defined because the k=1, σ=id subgroup is normal in the full stabilizer of T_S. Explicitly, choose any representative λ of (R,L), apply (3) with such k,σ and any corresponding flag matrix, and reconstruct (R',L'); different choices of flag matrix induce the same residual orbit. Thus, for each fixed S, exact orbits are those of an explicit finite semilinear action on admissible Grassmannian/projective pairs (R,L). To compare distinct S, use the maps (3) with kσ(S)=S'. This is an exact structural normal form and finite equivalence, not a closed formula for the number of orbits.

At exact source `feaf33e8b9f2725ac9b835a49dca95de4332171d`, GPT-6.1 Terra reviewers [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the full-root theorem, conditional on its cited C0004 and folder interfaces. Their reviews covered root-image forcing for every characteristic and rank, both directions of the parameterization, the semilinear isomorphism relation, and the fixed-S Grassmannian/projective normal form including rank-deficient matrices. No computation or fresh primary-source audit was performed. Other affine projection types remain outside this theorem.
