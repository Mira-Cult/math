# A finite simple proper Bol loop outside both G-loops and Bruck isotopes

## Theorem and scope

There exists a finite simple proper left Bol loop of order **3^75 · 19^3** that is not isomorphic to all its loop isotopes and is not isotopic to a Bruck loop.

Here *proper* means non-Moufang, *simple* means having no nontrivial proper normal subloop, a *G-loop* is isomorphic to each of its loop isotopes, and a left Bruck loop is a left Bol loop with the automorphic inverse property. The proof constructs one example and an explicitly nonisomorphic principal isotope. It does not classify all Bol loops or claim that this example is sporadic.

This is a standalone extraction of the existence argument at source commit `27d51e6a23363d6c0ae74b2f6f752db9bb5e5847`, from `odd-rigid-center-nongloop.md`. Lemmas A–G below replace its reliance on a general class-two classification. In particular no exhaustion theorem, general theorem on odd-order Bol envelopes, classification of finite simple groups, or Feit–Thompson theorem is needed. Basic finite-group facts used are conjugacy of complements for a normal Hall subgroup with solvable kernel, coprime averaging, and elementary properties of finite p-groups. The constructed groups are explicitly solvable.

**Review boundary.** The pinned source argument has received independent AI mathematical review. This extraction was written and self-checked by that reviewer. A separate AI mathematical review of an earlier textual version found no defect; the corrected textual version has not received a separate final review. Neither is a formally verified or human-refereed publication. Exact arithmetic and an independently implemented local section check accompany the proof. Priority and literature novelty are separate questions.

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

For the q-factor, take \(W_q=\mathbb F_{19}^2\), \(Z_q=\mathbb F_{19}\), \(\sigma_q=1\), \(b_q\) the standard alternating form, \(R_q(a)=\eta I\), \(R_q(d)=1\), and \(T_q=1\). These parameters define the group and its section in Lemma A below; W denotes one half of its noncentral coordinates. Both cross coprime fixed-space conditions and faithfulness hold.

Set the positive cocycle by
\[f_p(a)=1-\epsilon+\epsilon^2,\quad f_p(d)=0,\qquad f_q(d)=1,\quad f_q(a)=0.\tag{3}\]
In characteristic 3, \(1-\epsilon+\epsilon^2\) is a square root of \(1+\epsilon\), so \(T_p(a)\sigma_pf_p(a)=f_p(a)\). Extending by the crossed cocycle law gives \(f_p(a^3)=\epsilon^2\) and \(f_p(a^9)=0\). These data define the group and subgroup of Lemma A. We next verify its transversal test.

## Transversal proof

For a total torus label with nonzero \(d\)-coordinate, the q-center in the quadratic test in Lemma A is the nonzero value \(f_q(d^k)=k\). Its negative subgroup is zero and its quadratic term vanishes because \(R_q(a)\) is scalar and \(b_q\) alternating. Thus that coordinate blocks a collision.

For a nonzero pure \(a^t\) label, both negative subgroups in the p-center have zero constant coefficient. If \(t\not\equiv0\pmod3\), \(f_p(a^t)\) has nonzero constant coefficient. The quadratic term's constant coefficient is also zero: \((1-R_p(a^t))W_p\) is spanned by the first and third coordinate directions, and \(B_0\) annihilates those rows. This stays true with arbitrary individual d-labels whose total is zero, because their \(\lambda\)-scalars only multiply the second argument.

If \(t=3\) or 6, \(R_p(a^t)=1\), so the quadratic term is zero and \(f_p(a^t)=\pm\epsilon^2\). For an individual a-label \(j\pmod3\), the negative center line is
\[Z_p^-(a^j)=\mathbb F_3\bigl(\epsilon+(1-j)\epsilon^2\bigr).\tag{4}\]
When the two labels add to a multiple of 3, the two lines in the quadratic test coincide, even after the \(T_p(a^j)\) factor, and contain no nonzero \(\epsilon^2\). Thus no collision occurs. The Lemma A supplies a faithful generating Bol folder. Its order is |W_p||Z_p||W_q||Z_q|=3^75·19^3. Simplicity and direct properness are established separately below.

## Simple-loop test

Use the exhaustive τ-normal tuple description in Lemma B, writing its data as V_p,C_p,V_q,C_q,T,u and its stabilizer image as J_H≤T. No splitting of a normal subgroup's torus lifts is assumed. For either local factor, the map v↦v+τv injects V_i∩(W_i⊕0) into V_i^τ. Thus the local fixed-to-stabilizer-kernel ratio is at least |C_i^{σ_i}|, even when the two axis modules are isomorphic.

The T_p(a)-invariant central subgroups are exactly the single Jordan chain

    0 < ⟨ε²⟩ < ⟨ε,ε²⟩ < Z_p,

with σ-fixed orders 1,3,3,9. Any nonzero local normal vector part forces C_i≠0 by zero radical. For t∈T, normality makes T_i(t) act trivially on Z_i/C_i. Positivity of f_i(t) therefore makes its class σ_i-positive, while u_i(t) is σ_i-negative. The equation defining J_H can hold only if both classes vanish. Consequently

    |(J_H)_p| ≤ #{a^j:f_p(a^j)∈C_p} ≤ |C_p^{σ_p}|,
    |(J_H)_q| ≤ #{d^k:f_q(d^k)∈C_q} ≤ |C_q|.

For the p-chain the respective counts are 1,3,3,9: a label not divisible by three has nonzero constant coefficient, while f_p(a³)=ε² and f_p(a⁶)=−ε². The q counts are 1 or 19 because f_q is the central graph isomorphism. Thus each local contribution, after division by its component of |J_H|, is at least one.

If T has nonzero q-projection, it contains a pure nonidentity d^k. Its action on U_p has scalars λ^k,λ^{-k} different from one, forcing V_p=U_p and C_p=Z_p by normality and bracket generation. The exact p-local ratio is then 9. If the p-projection of T is proper in C₉, |(J_H)_p|≤3 leaves a strict factor. If both projections are full, a acts nontrivially on every q-axis by η^{±1}, forcing V_q=U_q and C_q=Z_q as well; then N=G.

If the q-projection is zero and the p-projection is nonzero, even a³ acts on the q-axes by η^{±3}≠1. Thus V_q=U_q,C_q=Z_q, while (J_H)_q=1, leaving a strict factor 19. Finally if T=1 and N≠1, some nonzero local intersection has nonzero C_i; every nonzero subgroup in the p-chain has a nonzero fixed element, and the q-center is fixed. Its local ratio is strict and J_H=1. Every nonidentity proper τ-normal tuple therefore has strict defect, proving simplicity by Lemma C.

## A direct Moufang failure

Let Q denote the full derived 19-Sylow group, and restrict to the actual subgroup

    G₀=(⟨ε²⟩×Q)⋊(⟨a³⟩×⟨d⟩).

Choose η=4, of order nine in F₁₉. The a³ action is trivial on the 3-center, scalar η³=7 on the first Q-axis and inverse scalar on the second. The stabilizer intersection is the Q first axis and the two central graph lifts a³↦ε², d↦1. The direct section calculation in Lemma D gives an actual ambient subloop: its section belongs to G₀∩K and is the unique ambient K-representative. In coordinates u∈F₁₉²,t∈F₃,s∈F₁₉ its product is

    (u,t,s)·(v,r,h)=(u+7^t v,t+r,s+h−γ(u,v)),

where γ is the standard alternating form. Choose X=(0,1,0), Y=((1,0),0,0), Z=((0,1),0,0). The final coordinates of (XY)(ZX) and (X(YZ))X are −7=12 and −1=18 in F₁₉. Thus the loop is non-Moufang directly, without a simple-Moufang classification input. No faithfulness of the restricted subgroup action is required.

## Obstruction to the shift isomorphism

Take \(z=\epsilon+\epsilon^2\in Z_p^-\). The normalized negative-central shift changes the p-cocycle by \((1-T_p(a))z=-\epsilon^2\). It corresponds to an actual principal isotope, as follows explicitly. Write τ̂ for the outside involution and Λ=τ̂K for its full outside class. Since τ(z)=z⁻¹, conjugation by z⁻¹ sends K=τ̂Λ to z⁻²K. Put k=z²∈K. The principal-isotope folder from Lemma E is (G,H,k⁻¹K); conjugating it by z gives (G,zHz⁻¹,K), whose cocycle is precisely f_z=f+(1−T)z. Thus the shifted datum is an isotope of the original loop, not just an unrelated selected cocycle. To prove this isotope is not isomorphic to Q, use the specialized strict isomorphism criterion proved in Lemma F, not mere center nonisomorphism.

Any isomorphism of data induces \(a\mapsto a^u\), \(u\in(\mathbb Z/9)^\times\), on the p-torus. On \(W_q=\mathbb F_{19}^2\), \(R_q(a)=\eta I\), so the intertwining equation forces \(\eta^u=\eta\), i.e. \(u=1\pmod9\). Then the center map must commute with \(T_p(a)\) and \(\sigma_p\), and transport \(f_p(a)\) to \(f_p(a)-\epsilon^2\). Since f_p(a) is a unit of F₃[ε]/(ε³), it generates Z_p as an F₃[T_p(a)]-module. A commuting center map is determined by its image on this vector, giving the unique possibility
\[M=1-\epsilon^2\quad\text{on }Z_p.\tag{5}\]
The q-torus generator may map to a power \(d^v\); its action on W_p is scalar \(\lambda\), which generates E over \(\mathbb F_3\). Thus any \(\mathbb F_3\)-linear intertwiner on W_p is E-semilinear, with the field part a Frobenius automorphism. Because the matrices (2) have \(\mathbb F_3\)-entries and trace is Frobenius-invariant, remove that field automorphism; it remains to find \(L\in\operatorname{GL}_4(E)\) commuting with \(R_p(a)\) and satisfying
\[L^TB_0L=B_0,\qquad L^TB_1L=B_1,\qquad L^TB_2L=B_2-B_0.\tag{6}\]
Every matrix commuting with \(\operatorname{diag}(J,J)\) has the form
\[L=\begin{pmatrix}a&b&c&d\\0&a&0&c\\e&f&g&h\\0&e&0&g\end{pmatrix}.\tag{7}\]
There is an elementary obstruction to the third congruence alone: the skew parts have different determinants in characteristic 3,
\[\det(B_2-B_2^T)=1,\qquad \det((B_2-B_0)-(B_2-B_0)^T)=0.\tag{8}\]
Congruence by an invertible matrix preserves the rank of the skew part, over every field extension, so no such L exists. This rank argument works over every extension of F₃ and does not require a Gröbner calculation, enumeration of invertible matrices or the additional R-commuting condition. The trace descent uses nondegeneracy: an identity Tr(xᵀCy)=0 for all x,y∈E⁴ forces the E-matrix C to vanish.

The original loop and this principal isotope are therefore nonisomorphic by Lemmas E and F. Lemma G excludes every Bruck isotope. The result gives an actual simple proper odd non-G-loop rather than a local bimap control. It does not classify other loops or establish literature novelty.


## Lemma A. The explicit group, transversal and canonical action

For each of the two primes let $U_i=W_i\oplus W_i$, and define

\[
 \Omega_i((x,y),(x',y'))=b_i(x,y')-b_i(x',y).
\]

Give $P_i=U_i\oplus Z_i$ the product

\[
 (v,z)(v',z')=(v+v',z+z'+\tfrac12\Omega_i(v,v')).
\]

Biadditivity gives associativity directly; the alternating form gives inverses $(-v,-z)$. Its commutator is $(0,\Omega_i(v,v'))$. Zero radical and spanning values show $Z(P_i)=P_i'=Z_i$. No general Lazard correspondence is needed for these explicit class-two groups.

Let $D=P_p\times P_q$, $G=D\rtimes A$, with $A$ acting by $R_i(t)\oplus R_i(t)^{-1}$ on $U_i$ and $T_i(t)$ on $Z_i$. The displayed compatibility identities make this an action by automorphisms. Let $\tau$ swap the two $W_i$ coordinates, apply $\sigma_i$ on $Z_i$, and invert $A$. It is an involutory automorphism: in particular

\[
 \Omega_i((y,x),(y',x'))=\sigma_i\Omega_i((x,y),(x',y')).
\]

Put $S_i=W_i\oplus0\oplus0$, $S=S_p\times S_q$,

\[
 H=S\rtimes\{f(t)t:t\in A\},\qquad K=\{g\in G:\tau(g)=g^{-1}\}.
\]

The crossed-cocycle equation makes the displayed graph a subgroup normalizing $S$. The center graph is written on the left of its torus label.

Above a label $t\in A$, the inverted elements have coordinates

\[
 (x_i,-R_i(t)^{-1}x_i,z_i),\quad z_i\in Z_{i,-}(t):=\ker(\sigma_i+T_i(t)^{-1}).
\]

Multiplying two such elements with labels $t,u$, membership in $H$ forces their second vector coordinate to vanish. The first coordinate then is $(1-R_i(tu))x_i$, and the possible center coordinates are

\[
 Z_{i,-}(t)+T_i(t)Z_{i,-}(u)
 +\{\tfrac12 b_i((1-R_i(tu))x,R_i(t)^{-1}x):x\in W_i\}.
\]

Thus for $tu\ne1$, exclusion of $f_i(tu)$ from this set in at least one factor is exactly the collision test $H\cap K^2=1$. If $tu=1$, membership gives zero vectors and zero center, so only the identity occurs.

The involutions $T_i(t)\sigma_i$ and $\sigma_i$ are conjugate using the unique square root of $t\in A$. Consequently

\[
 |K|=|A|\prod_i|W_i||Z_i^-|=\prod_i|W_i||Z_i|=[G:H],
\]

where $|A_p|=|Z_p^+|=9$ and $|A_q|=|Z_q^+|=19$. Since $K^{-1}=K$, the collision test makes $K$ a transversal to the cosets $gH$. The full inverted set is closed under $xyx$. A transversal with these two closure properties is a transversal to every conjugate of $H$: write $g=sh$, $s\in K,h\in H$, and use the bijection $u\mapsto sus$ of $K$ to transport cosets of $sHs^{-1}$ to cosets of $H$. Its coset multiplication $x*y\in K\cap xyH$ is a loop and satisfies the left Bol identity because $xyx\in K$.

For generation, in the extension $G\rtimes\langle\widehat\tau\rangle$, all outside involutions are conjugate, by conjugacy of complements to the normal odd solvable subgroup $G$. Their products generate a normal subgroup of $G$, namely $\langle K\rangle$. Pure $A$ lies in $K$. The cross-prime actions have no common fixed vectors on $U_i$; hence commutators with $A$ generate $U_i$ modulo $Z_i$. Their normal closure then contains all $P_i$, because $P_i'=Z_i$. Thus $\langle K\rangle=G$ and $G'=D$.

Finally $H\cap Z(D)=1$. Any normal subgroup of $G$ contained in $H$ has trivial intersection with $D$: a nontrivial normal subgroup of a finite p-group meets its center. It therefore centralizes $D$. The combined $R_i$-action is faithful, so $C_G(D)=Z(D)$, and the subgroup is trivial. The action on $G/H$ is faithful. Since $K$ generates, this is exactly the left multiplication group of the loop.

## Lemma B. All invariant normal subgroups and their defect

For these explicit data, every $\tau$-invariant normal subgroup $N\lhd G$ has the following description. Choose $A$- and $\tau$-invariant subspaces $V_i\le U_i$, $C_i\le Z_i$ with

\[
 \Omega_i(V_i,U_i)\subseteq C_i.
\]

Let $T\le A$ be the image of $N$, satisfying

\[
 (\rho_i(t)-1)U_i\subseteq V_i,\qquad (T_i(t)-1)Z_i\subseteq C_i\quad(t\in T),
\]

where $\rho_i=R_i\oplus R_i^{-1}$. There is a homomorphism

\[
 u:T\longrightarrow\prod_i((Z_i/C_i)^A)^-
\]

such that the elements of $N$ with label $t$ have vector coordinates in $V_i$ and center coordinates equal to $u_i(t)$ modulo $C_i$.

Here is why no subgroups or nonsplit lifts are lost. In a class-two group of odd exponent p, a subgroup is closed under the additive law $xy[x,y]^{-1/2}$, so is an $\mathbb F_p$-subspace; normality supplies the bracket condition. Average under the cross-prime subgroup $B_i\le A$, which fixes $Z_i$ and has no fixed vector on $U_i$. This separates $N\cap P_i$ into $V_i\oplus C_i$, removing any central graph offset. For a lift of $t\in T$, commutators with $B_i$ and averaging put its vector part in $V_i$; remove it. The remaining center class is fixed by $A$, by normality. Normality under $P_i$ gives the two displacement inclusions. The action of $T$ on $Z_i/C_i$ is therefore trivial, so the lift classes form an ordinary homomorphism $u$; $\tau$-stability makes them negative. Conversely these conditions close the subgroup under multiplication, conjugation and $\tau$. In conjugation by a vector, the extra BCH term lies in $C_i$ by the bracket condition and displacement inclusion.

Let

\[
 J_H=\{t\in T:f_i(t)+C_i=u_i(t)\text{ for both }i\}.
\]

Fixed elements have trivial torus image, whereas $H\cap N$ has torus image $J_H$. Counting kernels gives

\[
 \frac{|C_N(\tau)|}{|H\cap N|}
 =\frac{\prod_i |C_i^{\sigma_i}|\,|V_i^\tau|}
 {|J_H|\prod_i|V_i\cap(W_i\oplus0)|}.
\]

This proves the exact test used above, including the possibility of isomorphic or overlapping composition factors in the two axes.

## Lemma C. Why strict defect proves simplicity

Let $(G,H,K)$ be a faithful generating left Bol folder with $G$ odd and solvable and $K$ its full inverted set for $\tau$. Suppose

\[
 |H\cap N|<|C_N(\tau)|
\]

for every nontrivial proper $\tau$-invariant normal subgroup $N\lhd G$. Then its loop is simple.

First, coprime complement conjugacy gives $C_G(\tau)\twoheadrightarrow C_{G/N}(\tau)$; it also says that the image of $K$ is the full inverted set of $G/N$. Hence

\[
 \frac{|KN/N|}{[G:HN]}=\frac{|C_N(\tau)|}{|H\cap N|}.
\]

Equality holds exactly when the projected section is a transversal. It then defines the quotient loop, with the natural projection a homomorphism.

To prove sufficiency without assuming that every quotient kernel is $\tau$-invariant, suppose a nontrivial proper normal subloop exists and enlarge it to a maximal one $P$. Then $Q/P$ is simple. The induced epimorphism $G\to\operatorname{LMlt}(Q/P)$ has nontrivial proper kernel $N$, and the preimage of its identity stabilizer is $HN$. If the simple quotient is associative, its left multiplication group is solvable, so it is cyclic of prime order and has an inversion automorphism. If it is nonassociative, it also has an automorphism inverting its left translations, by the elementary argument in the next paragraph. Agreement on generating translations therefore makes $N$ $\tau$-invariant. The projected section is precisely the translations of $Q/P$, so the displayed ratio is one, a contradiction.

For completeness, a simple nonassociative left Bol loop has trivial left nucleus. The left and middle nuclei coincide and are normal: the Bol identity gives the autotopism $(L_xR_x,L_x^{-1},L_x)$; conjugating $(L_a,1,L_a)$ for a left-nuclear $a$ shows $L_xL_aL_x^{-1}=L_c$ with $c$ left-nuclear, and $x*a=c*x$. It follows that $x*(a*z)=(x*a)*z$, so the left nucleus is contained in the middle nucleus. Conversely the middle-nucleus identity together with Bol gives $(a*y)*w=a*(y*w)$. The resulting subgroup $N_\lambda=N_\mu$ has $xN=Nx$ and its cosets multiply as $(Nx)(Ny)=N(xy)$, giving a normal subloop. In a simple nonassociative loop it is therefore trivial.

Now, if $k_1\cdots k_m=1$ is a relation among its left translations, the generatorwise-inverted word $k_1^{-1}\cdots k_m^{-1}$, denoted $g$, satisfies $gK\subseteq K$, by repeated sandwich closure: the reverse of its defining word is one. Taking the identity shows $g=L_a$; the inclusion says $L_aL_y=L_{a*y}$ for every $y$, hence $a$ is left-nuclear and $g=1$. Thus inverting each generator respects all relations, defining the required involutory automorphism. This proves the only nontrivial loop-theoretic input in the simple-quotient argument.

## Lemma D. The local product used for properness

Write the 19-group as $W\oplus W\oplus\mathbb F_{19}$, $W=\mathbb F_{19}^2$, with

\[
 (x,y,c)(X,Y,C)=(x+X,y+Y,c+C+\tfrac12[\gamma(x,Y)+\gamma(y,X)]).
\]

The relevant 3-torus generator acts as $(7,7^{-1},1)$. The auxiliary central 3-coordinate and 19-coordinate are tied to their torus labels in the stabilizer, while its first $W$-axis is free. For a loop coordinate $(u,t,s)$, a section representative has $W$-coordinates $(-7^{-t}u,u)$, zero centers, and torus labels $(-t,-s)$. It is inverted by $\tau$. Multiplying two representatives and reducing by the stabilizer gives

\[
 (u,t,s)*(v,r,h)=(u+7^tv,t+r,s+h-\gamma(u,v)).
\]

One can check the last coordinate without any implicit group identification: if a product has first and second vector coordinates $x,y$, center $c$, and torus labels $j,k$, its section representative has first vector $-7^j y$. Right multiplication by the first-axis stabilizer changes the center by $\tfrac12\gamma(y,-7^j y-x)$; cancelling this center using the graph label yields exactly the displayed expression. The central 3-coordinate is zero for these products. These representatives belong to the original $K$ and lie in the subgroup displayed in the main proof; uniqueness of the ambient section proves this is an actual subloop, not merely a formal auxiliary operation.

## Lemma E. The principal-isotope interface

Every loop isotope is isomorphic to a principal isotope $x\circ y=R_a^{-1}(x)*L_b^{-1}(y)$. This follows by transporting an isotopy through its third bijection and then identifying the new identity. The left Bol autotopism $(L_aR_a,L_a^{-1},L_a)$, derived directly from the Bol identity, changes variables by $X=L_a(x)$ and $Y=L_a(y)$ to a product

\[
 X\odot Y=X*L_d^{-1}(Y),\qquad d=a*(b*a),\qquad L_d=L_aL_bL_a.
\]

Its translation set is $Kk^{-1}$, $k=L_d$, and its identity is $d$. Its generated left multiplication group remains $G$: the shifted set contains $k^{-1}$ and recovers every element of $K$ by multiplication by $k$. Its stabilizer is $kHk^{-1}$. Conjugating the action by $k^{-1}$ gives the folder $(G,H,k^{-1}K)$. Conversely every $k\in K$ occurs. The shifted set is inverse- and sandwich-closed, as follows by the same properties of $K$, so it again gives a Bol loop.

In this shifted folder the inverting automorphism is

\[
 \tau_k=\operatorname{Inn}(k^{-1})\circ\tau,
\]

as is verified on $k^{-1}K$. A loop with such an automorphism has the automorphic inverse property exactly when $\tau_k(H)=H$: if the stabilizer is preserved, the permutation $gH\mapsto\tau_k(g)H$ is inversion and is a loop automorphism; conversely loop inversion induces this automorphism on the generating translations. Therefore a Bruck isotope exists exactly when $H$ and $\tau(H)$ are conjugate in $G$, since any conjugator is $kh$, $k\in K,h\in H$.

## Lemma F. The strict isomorphism test for these examples

Any loop isomorphism induces an isomorphism of its canonical left multiplication groups carrying $H,K$ to their counterparts. It preserves the involution, since that is determined by its values on generating $K$. It preserves $D=G'$, its two characteristic Sylow subgroups, their centers, $S=H\cap D$, and $\tau S$.

In the explicit class-two groups the additive law is recovered from multiplication as $xy[x,y]^{-1/2}$. Consequently on $P_i=S_i\oplus\tau S_i\oplus Z_i$, an isomorphism is exactly of the form $(L_i,L_i,M_i)$, with no mixing or central shear, and

\[
 M_i\sigma_i=\sigma_i'M_i,\qquad M_i b_i(x,y)=b_i'(L_ix,L_iy).
\]

Let $E:A\to A'$ be the induced quotient isomorphism. Write the image of a pure torus element $t$ as $v(t)E(t)$, with $v(t)\in D'$. Preservation of the stabilizer graph puts the vector part of $v(t)$ in the first axis. The pure element $t$ is inverted by $\tau$, so its image is inverted by $\tau'$; the explicit equation for inverted elements forces that vector part to vanish. Thus $v(t)$ is central. Conjugating $D'$ gives the action intertwining equations

\[
 L_iR_i(t)=R_i'(E(t))L_i,\qquad M_iT_i(t)=T_i'(E(t))M_i.
\]

Preservation of the stabilizer graph then says $v(t)=f'(E(t))-Mf(t)$. This vector is positive for $T'(E(t))\sigma'$, by the cocycle positivity condition. Inversion of $v(t)E(t)$ says it is negative for the same involution. Odd characteristic makes it zero. Therefore

\[
 M_if_i(t)=f_i'(E(t)).
\]

These are necessary and sufficient conditions: sufficiency follows by substituting into the group multiplication. This derives the strict criterion needed for the rank obstruction without any exhaustion theorem or assumed G-loop property.

## Lemma G. Excluding Bruck isotopy directly

For the explicit group, $G'=D$, $A=G/D\cong C_9\times C_{19}\ne1$, and $H$ surjects onto $A$. In $G^+=G\rtimes\langle\widehat\tau\rangle$, let $\Lambda=\widehat\tau^G=\widehat\tau K$. By Lemma A, $H\cap\Lambda^2=1$.

If $H$ and $\tau(H)$ were $G$-conjugate, some element of the outside coset would normalize $H$. Its order is twice an odd number; an odd power gives an outside involution $\lambda$ still normalizing $H$. Complement conjugacy makes $\lambda\in\Lambda$. For every $h\in H$,

\[
 h^{-1}h^\lambda=\lambda^h\lambda\in H\cap\Lambda^2=1.
\]

Thus $\lambda$ centralizes $H$. But its conjugation induces inversion on $A$, while $H$ surjects onto $A$. This would force every element of the nontrivial odd group $A$ to equal its inverse, impossible. Lemma E now excludes all Bruck isotopes.


## Reproducibility and relationship to the original framework

The original finite arithmetic certificate is `verify_odd_rigid_center.py`. It checks matrices, cocycles, negative-center lines, field orders, the rank obstruction and the Moufang witness using exact modular integers. The supplementary `independent_bch_section_check.py` independently computes the local BCH group product and right-stabilizer reduction; 10,000 comparisons with a fixed random seed agree with Lemma D. Both ran under Python 3.12.14. Neither constructs the entire loop, proves universal subgroup statements by enumeration, or constitutes formal verification.

The larger `odd-class-two-classification.md` develops a proposed construction/exhaustion/isomorphism theorem for the whole class-two-derived branch. Its constructive formulas motivated this example. The present proof deliberately does not depend on its exhaustion direction. The original source manuscripts and their revision-specific review records should be retained alongside this simplified proof, with their broader scope and qualifications unchanged.

The historical question is Nagy, *Some remarks on simple Bol loops*, Commentationes Mathematicae Universitatis Carolinae **49** (2008), 259–270, §6 Problem 1: a simple Bol loop outside the G-loop and Bruck-isotope classes. The finite example above would answer that existence question. [Primary paper](https://cmuc.karlin.mff.cuni.cz/pdf/cmuc0802/nagy.pdf). This historical match does not establish current priority or settle the classification of finite simple Bol loops.
