# A simple odd Bol loop with a nonisomorphic principal isotope

**Continuation of 0323:C0010 [context outside this selected packet: `../claims/C0010.md`], with four independent proof/code acceptances recorded below.** The result is an explicit simple proper odd left Bol loop of order 3^75·19^3 with a nonisomorphic principal isotope. Thus it is not a G-loop (a loop isomorphic to every one of its loop isotopes). The reviewed odd nonconjugacy theorem also excludes Bruck isotopy. This is an existence result, not an exhaustive classification or a literature-novelty claim.

The construction, exhaustive normal-subgroup test and strict isomorphism relation use the [whole-class-two theorem](odd-class-two-classification.md), reviewed at `226a8dc1eb503026c350ffe3b7ac93da9077a593`, with its pinned folder and strict-defect dependencies. The arbitrary principal-isotope interface is the [separately reviewed calculation](exact-factorization-criterion.md#bruck-isotopy-as-a-stabilizer-conjugacy-test) at `ea836a5f328d6bc52913aac8fd1841a87072f5f8`; no aggregate acceptance of C0012 is assumed. The actual subloop Moufang calculation below uses the fixed-central coordinates reviewed at `722ba8c289c96dfd87c98f9a5ab3dcb8b2080998`.

## Data

Let \(p=3\), \(q=19\), \(E=\mathbb F_{3^{18}}\), choose \(\lambda\in E^\times\) of order 19, and choose \(\eta\in\mathbb F_{19}^\times\) of order 9. The multiplicative orders are \(\operatorname{ord}_{19}(3)=18\) and \(\operatorname{ord}_9(19)=1\). Let \(A=\langle a\rangle\times\langle d\rangle\cong C_9\times C_{19}\). On the p-factor put
\[Z_p=\mathbb F_3[\epsilon]/(\epsilon^3),\quad T_p(a)z=(1+\epsilon)z,\quad T_p(d)=1,\quad \sigma_p(\epsilon)=-\epsilon+\epsilon^2.\]
Thus \(T_p(a)\) has order 3, while a itself has order 9; \(\sigma_pT_p(a)\sigma_p=T_p(a)^{-1}\). Its plus subgroup has order 9 and its minus subgroup is \(\mathbb F_3(\epsilon+\epsilon^2)\).

Let \(W_p=E^4\), with \(R_p(a)=\operatorname{diag}(J,J)\), \(J=\left(\begin{smallmatrix}1&1\\0&1\end{smallmatrix}\right)\), and \(R_p(d)=\lambda I\). Define
\[b_p(x,y)=\operatorname{Tr}_{E/\mathbb F_3}\bigl(x^T(B_0+B_1\epsilon+B_2\epsilon^2)y\bigr),\tag{1}\]
using the explicit matrices over \(\mathbb F_3\):
\[B_0=\begin{pmatrix}0&0&0&0\\0&0&0&1\\0&0&0&0\\0&2&0&0\end{pmatrix},\quad
B_1=\begin{pmatrix}0&0&0&2\\0&1&1&0\\0&1&0&0\\2&0&0&0\end{pmatrix},\quad
B_2=\begin{pmatrix}0&2&1&1\\1&1&0&2\\2&2&0&0\\0&1&0&0\end{pmatrix}.\tag{2}\]
Writing R=R_p(a), direct multiplication gives B₀ᵀ=−B₀, B₁ᵀ=B₁, B₂ᵀ=−B₁−B₂, and RᵀB_iR⁻¹=B_i+B_{i−1}, where B_{−1}=0. These are precisely σ_p b_p(x,y)=−b_p(y,x) and b_p(Rx,R⁻¹y)=T_p(a)b_p(x,y). One has det B₁=1, so nondegeneracy of the field trace gives zero left and right radicals and hence zero radical for Ω_p. The B_i are linearly independent: their coefficients in positions (2,4),(1,4),(1,3) form an invertible three-by-three matrix. Trace nondegeneracy then makes the values of b_p span Z_p. The λ-scalar compatibility is immediate since the two inputs scale inversely.

For the q-factor, take \(W_q=\mathbb F_{19}^2\), \(Z_q=\mathbb F_{19}\), \(\sigma_q=1\), \(b_q\) the standard alternating form, \(R_q(a)=\eta I\), \(R_q(d)=1\), and \(T_q=1\). These are the normal-form parameters, not the full first-plus-second-half group coordinates. Both cross coprime fixed-space conditions and faithfulness hold.

Set the positive cocycle by
\[f_p(a)=1-\epsilon+\epsilon^2,\quad f_p(d)=0,\qquad f_q(d)=1,\quad f_q(a)=0.\tag{3}\]
In characteristic 3, \(1-\epsilon+\epsilon^2\) is a square root of \(1+\epsilon\), so \(T_p(a)\sigma_pf_p(a)=f_p(a)\). Extending by the crossed cocycle law gives \(f_p(a^3)=\epsilon^2\) and \(f_p(a^9)=0\). These data define the BCH folder \((G,H,K)\) in the reviewed construction, subject to its selection tests.

## Transversal proof

For a total torus label with nonzero \(d\)-coordinate, the q-center in the reviewed quadratic test is the nonzero value \(f_q(d^k)=k\). Its negative subgroup is zero and its quadratic term vanishes because \(R_q(a)\) is scalar and \(b_q\) alternating. Thus that coordinate blocks a collision.

For a nonzero pure \(a^t\) label, both negative subgroups in the p-center have zero constant coefficient. If \(t\not\equiv0\pmod3\), \(f_p(a^t)\) has nonzero constant coefficient. The quadratic term's constant coefficient is also zero: \((1-R_p(a^t))W_p\) is spanned by the first and third coordinate directions, and \(B_0\) annihilates those rows. This stays true with arbitrary individual d-labels whose total is zero, because their \(\lambda\)-scalars only multiply the second argument.

If \(t=3\) or 6, \(R_p(a^t)=1\), so the quadratic term is zero and \(f_p(a^t)=\pm\epsilon^2\). For an individual a-label \(j\pmod3\), the negative center line is
\[Z_p^-(a^j)=\mathbb F_3\bigl(\epsilon+(1-j)\epsilon^2\bigr).\tag{4}\]
When the two labels add to a multiple of 3, the two lines in the quadratic test coincide, even after the \(T_p(a^j)\) factor, and contain no nonzero \(\epsilon^2\). Thus no collision occurs. The construction theorem supplies a faithful generating Bol folder. Its order is |W_p||Z_p||W_q||Z_q|=3^75·19^3. Simplicity and direct properness are established separately below.

## Simple-loop test

Use the exhaustive τ-normal tuple test in the reviewed classification, writing its data as V_p,C_p,V_q,C_q,T,u and its stabilizer image as J_H≤T. No splitting of a normal subgroup's torus lifts is assumed. For either local factor, the map v↦v+τv injects V_i∩(W_i⊕0) into V_i^τ. Thus the local fixed-to-stabilizer-kernel ratio is at least |C_i^{σ_i}|, even when the two axis modules are isomorphic.

The T_p(a)-invariant central subgroups are exactly the single Jordan chain

    0 < ⟨ε²⟩ < ⟨ε,ε²⟩ < Z_p,

with σ-fixed orders 1,3,3,9. Any nonzero local normal vector part forces C_i≠0 by zero radical. For t∈T, normality makes T_i(t) act trivially on Z_i/C_i. Positivity of f_i(t) therefore makes its class σ_i-positive, while u_i(t) is σ_i-negative. The equation defining J_H can hold only if both classes vanish. Consequently

    |(J_H)_p| ≤ #{a^j:f_p(a^j)∈C_p} ≤ |C_p^{σ_p}|,
    |(J_H)_q| ≤ #{d^k:f_q(d^k)∈C_q} ≤ |C_q|.

For the p-chain the respective counts are 1,3,3,9: a label not divisible by three has nonzero constant coefficient, while f_p(a³)=ε² and f_p(a⁶)=−ε². The q counts are 1 or 19 because f_q is the central graph isomorphism. Thus each local contribution, after division by its component of |J_H|, is at least one.

If T has nonzero q-projection, it contains a pure nonidentity d^k. Its action on U_p has scalars λ^k,λ^{-k} different from one, forcing V_p=U_p and C_p=Z_p by normality and bracket generation. The exact p-local ratio is then 9. If the p-projection of T is proper in C₉, |(J_H)_p|≤3 leaves a strict factor. If both projections are full, a acts nontrivially on every q-axis by η^{±1}, forcing V_q=U_q and C_q=Z_q as well; then N=G.

If the q-projection is zero and the p-projection is nonzero, even a³ acts on the q-axes by η^{±3}≠1. Thus V_q=U_q,C_q=Z_q, while (J_H)_q=1, leaving a strict factor 19. Finally if T=1 and N≠1, some nonzero local intersection has nonzero C_i; every nonzero subgroup in the p-chain has a nonzero fixed element, and the q-center is fixed. Its local ratio is strict and J_H=1. Every nonidentity proper τ-normal tuple therefore has strict defect, proving simplicity under the cited criterion.

## A direct Moufang failure

Let Q denote the full derived 19-Sylow group, and restrict to the actual subgroup

    G₀=(⟨ε²⟩×Q)⋊(⟨a³⟩×⟨d⟩).

Choose η=4, of order nine in F₁₉. The a³ action is trivial on the 3-center, scalar η³=7 on the first Q-axis and inverse scalar on the second. The stabilizer intersection is the Q first axis and the two central graph lifts a³↦ε², d↦1. The fixed-central section calculation reviewed at `722ba8c289c96dfd87c98f9a5ab3dcb8b2080998` is therefore an actual ambient subloop: its section belongs to G₀∩K and is the unique ambient K-representative. In coordinates u∈F₁₉²,t∈F₃,s∈F₁₉ its product is

    (u,t,s)·(v,r,h)=(u+7^t v,t+r,s+h−γ(u,v)),

where γ is the standard alternating form. Choose X=(0,1,0), Y=((1,0),0,0), Z=((0,1),0,0). The final coordinates of (XY)(ZX) and (X(YZ))X are −7=12 and −1=18 in F₁₉. Thus the loop is non-Moufang directly, without a simple-Moufang classification input. No faithfulness of the restricted subgroup action is required.

## Obstruction to the shift isomorphism

Take \(z=\epsilon+\epsilon^2\in Z_p^-\). The normalized negative-central shift changes the p-cocycle by \((1-T_p(a))z=-\epsilon^2\). It corresponds to an actual principal isotope, as follows explicitly. Write τ̂ for the outside involution and Λ=τ̂K for its full outside class. Since τ(z)=z⁻¹, conjugation by z⁻¹ sends K=τ̂Λ to z⁻²K. Put k=z²∈K. The reviewed principal-isotope folder is (G,H,k⁻¹K); conjugating it by z gives (G,zHz⁻¹,K), whose cocycle is precisely f_z=f+(1−T)z. Thus the shifted datum is an isotope of the original loop, not just an unrelated selected cocycle. To prove this isotope is not isomorphic to Q, use the reviewed **strict** isomorphism criterion (15), not mere center nonisomorphism.

Any isomorphism of data induces \(a\mapsto a^u\), \(u\in(\mathbb Z/9)^\times\), on the p-torus. On \(W_q=\mathbb F_{19}^2\), \(R_q(a)=\eta I\), so the intertwining equation forces \(\eta^u=\eta\), i.e. \(u=1\pmod9\). Then the center map must commute with \(T_p(a)\) and \(\sigma_p\), and transport \(f_p(a)\) to \(f_p(a)-\epsilon^2\). Since f_p(a) is a unit of F₃[ε]/(ε³), it generates Z_p as an F₃[T_p(a)]-module. A commuting center map is determined by its image on this vector, giving the unique possibility
\[M=1-\epsilon^2\quad\text{on }Z_p.\tag{5}\]
The q-torus generator may map to a power \(d^v\); its action on W_p is scalar \(\lambda\), which generates E over \(\mathbb F_3\). Thus any \(\mathbb F_3\)-linear intertwiner on W_p is E-semilinear, with the field part a Frobenius automorphism. Because the matrices (2) have \(\mathbb F_3\)-entries and trace is Frobenius-invariant, remove that field automorphism; it remains to find \(L\in\operatorname{GL}_4(E)\) commuting with \(R_p(a)\) and satisfying
\[L^TB_0L=B_0,\qquad L^TB_1L=B_1,\qquad L^TB_2L=B_2-B_0.\tag{6}\]
Every matrix commuting with \(\operatorname{diag}(J,J)\) has the form
\[L=\begin{pmatrix}a&b&c&d\\0&a&0&c\\e&f&g&h\\0&e&0&g\end{pmatrix}.\tag{7}\]
There is an elementary obstruction to the third congruence alone: the skew parts have different determinants in characteristic 3,
\[\det(B_2-B_2^T)=1,\qquad \det((B_2-B_0)-(B_2-B_0)^T)=0.\tag{8}\]
Congruence by an invertible matrix preserves the rank of the skew part, over every field extension, so no such L exists. This rank argument works over every extension of F₃ and does not require a Gröbner calculation, enumeration of invertible matrices or the additional R-commuting condition. The trace descent uses nondegeneracy: an identity Tr(xᵀCy)=0 for all x,y∈E⁴ forces the E-matrix C to vanish.

The original loop and this principal isotope are therefore nonisomorphic under the cited structural and isotope interfaces. The reviewed odd stabilizer-nonconjugacy theorem at `e896039d004ff3882621aca115b1a39cc8fed207`, together with the Bruck-isotopy criterion at `ea836a5f328d6bc52913aac8fd1841a87072f5f8`, also excludes a Bruck isotope. The result gives an actual simple proper odd non-G-loop rather than a local bimap control. It does not classify other loops or establish literature novelty.

## Arithmetic evidence and review scope

The standalone [arithmetic control](../code/verify_odd_rigid_center.py) checks the displayed F₃ matrices, cocycle/negative-line data, local center bounds, semilinear field orders and direct Moufang witness using exact integers modulo 3 and 19. It does not construct F_{3^18}, enumerate the huge loop, prove the universal subgroup/interface steps, or formally verify the argument. The finite identities supplement the analytic proof above. At exact source `88214700dc527d238d5754029711752495c9a292`, GPT-6.1 Terra reviewers [model reviewer identity omitted], [model reviewer identity omitted], [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the complete construction and each read and ran the committed arithmetic certificate. Their reviews checked all matrix/trace and crossed-cocycle inputs, every mixed-label transversal case, all τ-normal defects including nonsplit central lifts and isomorphic axis modules, canonical faithfulness/generation, the actual ambient Moufang subloop, the principal-isotope conjugation direction, and every torus/center/semilinear possibility in the isomorphism obstruction. The fourth reviewer separately rederived the specialized quadratic and normal-tuple tests and the strict isomorphism argument, including why no extra complement cochain survives. All retain the cited canonical-folder, strict-defect, class-two and isotope interfaces.

The root and three reviewers used bundled Python 3.12.14. The fourth run was reported as `python3` without a version claim. The root command was `python3 problems/0323-finite-simple-non-moufang-bol-loops/code/verify_odd_rigid_center.py` using that pinned executable; reviewers extracted the exact committed script with `git show 88214700dc527d238d5754029711752495c9a292:problems/0323-finite-simple-non-moufang-bol-loops/code/verify_odd_rigid_center.py`. Every reported run returned `rigid-center arithmetic passed; direct Moufang central values: 12 and 18`. No huge-loop enumeration, formal verification or literature priority was claimed.

The separate [primary-source question audit](../REFERENCES.md#simple-bol-loops-outside-both-historical-classes) identifies Nagy's 2008 §6 Problem 1 as asking for a simple Bol loop outside both G-loops and Bruck isotopes, without a finiteness restriction. Under the reviewed inputs this finite example answers that existence question; opposites transport the left convention. The later 2021 status report and bounded current search do not establish priority or current literature novelty. This resolution of one existence question does not resolve the unrestricted classification.
