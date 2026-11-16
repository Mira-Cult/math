# An odd-envelope quotient constraint

This manuscript addresses the odd-envelope part of the residual
classification in C0010 [context outside this selected packet: `../claims/C0010.md`]. The separate
[exact-factorization criterion](exact-factorization-criterion.md) gives a
possible endpoint; no implication to that criterion is proved here.

Let (G,H,K) be a finite faithful generating left Bol folder for a simple nonassociative loop Q, with G of odd order. Assume an involution τ∈Aut(G) inverts K and τK is invariant under G-conjugacy. (The invoked parts of C0001/C0007 are not reviewed here.) Put C=C_G(τ). In G⋊⟨τ⟩ all involutions are G-conjugate by conjugacy of complements to G, so τK is the full class of τ, and K={g:τ(g)=g⁻¹}. In particular |K|=[G:C], whence |H|=|C|. This assumes odd G; no claim is made here that all odd-order Bol loops have odd G.

Let V be any nonzero τ-stable elementary abelian normal subgroup of G (minimality is not needed). Set V_+=C_V(τ), V_-={v∈V:τ(v)=v⁻¹}. Then V=V_+⊕V_- because |V| is odd. Let bars denote reduction modulo V. The map C_G(τ)→C_{G/V}(τ) is onto: for a fixed coset gV, the two complements ⟨τ⟩ and ⟨g⁻¹τg⟩ of V in V⋊⟨τ⟩ are conjugate by V. Thus |C_{G/V}(τ)|=|C|/|V_+|. Moreover K maps onto the full inverted set K̄ in G/V: this is the conjugacy class of τ in the quotient, and every conjugator lifts. Hence

|K̄|=|K|/|V_-|,   K∩V=V_-,   |K̄|/[G:HV]=|V_+|/|H∩V|.   (∗)

The image K̄ covers every left coset of HV/V, since K covers every H-coset. Therefore |H∩V|≤|V_+|. Equality holds iff K̄ is a transversal to HV/V. In that case the projection K→K̄ is a surjective loop homomorphism, with kernel V_-. Indeed if a,b,c∈K and ab∈cH, their images satisfy the analogous relation, and uniqueness in the quotient determines the product. No general quotient homomorphism is claimed without equality.

Consequently, if Q is simple nonassociative and V_-≠1, then either HV=G or |H∩V|<|V_+|: equality with HV<G would yield a nontrivial proper kernel. In fact V_+≠1 always. Otherwise V_-=V, and (∗) forces H∩V=1 and equality; simplicity forces HV=G. The abelian normal subgroup V is then transitive and, by faithfulness, regular: H∩V=1. Thus |K|=|V| and K∩V=V imply K=V. Generation gives G=V and H=1, making Q associative, contradiction.

This gives a necessary obstruction to a τ-anti-fixed elementary abelian normal subgroup, including any τ-stable minimal normal subgroup, without asserting that τ swaps two distinct minimal normal subgroups. A τ-stable irreducible normal subgroup may still have both ± eigenspaces, and strict inequality in (∗) exactly identifies the enlarged-stabilizer case not handled by this quotient argument. The elementary abelian requirement is automatic for a minimal nontrivial normal subgroup of G⋊⟨τ⟩ if that group is solvable, but such a subgroup need not be minimal normal in G. These observations neither prove exact-factorization existence nor classify odd-order loops. The scoped independent review is recorded below.
# Mixed eigenspaces occur in faithful generating odd Bol folders

This is a nonsimple control with the scoped review below. Let p and q be odd primes with ord_q(p)=2m. Put F=F_{p^{2m}}, E=F_{p^m}, σ(z)=z^{p^m}, and choose ζ∈F of order q. Then σ(ζ)=ζ^{-1}. Let G=F^+⋊⟨a⟩, where a acts on F by multiplication by ζ. Define τ(v,a^i)=(σ(v),a^{-i}), H=E^+≤F^+, and K={g∈G:τ(g)=g^{-1}}. The order of G is odd. The subgroup V=F^+ is an irreducible minimal normal subgroup of G, τ-stable, with nonzero + and − eigenspaces E and ker(σ+1), each of dimension m.

Explicitly K consists of all (v,a^i) such that v+ζ^i σ(v)=0. Each fiber has p^m elements, and |K|=q p^m=[G:H]. For h∈G, H^h=ζ^r E for some r. If two elements of K lie in the same left coset of H^h, their second coordinates agree, say a^i, and the difference δ of their first coordinates lies in ζ^{i+r}E. Since both satisfy v+ζ^iσ(v)=0, δ+ζ^iσ(δ)=0. Writing δ=ζ^{i+r}t with t∈E gives δ+ζ^iσ(δ)=(ζ^{i+r}+ζ^{-r})t. The coefficient cannot vanish: ζ has odd order, so ζ^{i+2r}≠−1. Hence δ=0. Counting shows K is a transversal to every conjugate of H. K is inverse closed and closed under x y x because τ inverts each of x,y,xyx. Thus the standard folder criterion gives a left Bol loop. The core of H is zero: ∩_r ζ^r E is an invariant additive subgroup of irreducible V and lies properly in V, so the folder is faithful.

The projection of K to ⟨a⟩ is surjective. Also K∩V=ker(σ+1) is nonzero, and a^2 is a projection of a product of K elements. Because G has odd order, a lift of a^2 generates the same cyclic subgroup as an appropriate odd power, and its conjugation on V is scalar ζ². Consequently the span of the conjugates of any nonzero vector in K∩V is the whole irreducible module V (since ord_q(p)=2m and ζ² generates C_q). Hence ⟨K⟩ contains V and projects onto ⟨a⟩, so equals G.

The loop is not simple: HV=V is proper and H∩V=E=C_V(τ), so the quotient criterion of odd-folder-radicals.md gives a surjective homomorphism onto the order-q loop with kernel K∩V of order p^m. For a concrete example take p=3, q=7, m=3, so |G|=3^6·7 and |Q|=3^3·7. Thus mixed ± eigenspaces in a τ-stable minimal normal subgroup cannot be ruled out using only odd order, faithfulness, generation and the Bol folder axioms; simplicity is essential. This does not answer whether simplicity can rule them out.

## Scoped independent review

At exact revision `15ec5fb55fba8e614b180cff75e95516031285b6`, [model reviewer identity omitted] accepted the counting identity, quotient-transversality criterion, simplicity obstruction and mixed-eigenspace control under the stated odd-order and involution hypotheses, upstream folder criterion and standard complement conjugacy. The control has quotient order 7 and kernel order 27 at the stated parameters. This review makes no assertion that every odd-order Bol loop has odd-order multiplication group, proves no exhaustiveness and supplies no simple example; no computation or formal verification was performed.
## Further structural reductions

The equality alternative in the earlier manuscript can be removed entirely for a simple nonassociative Q. Let A≠1 be any τ-stable **abelian** normal subgroup of odd G, not necessarily elementary abelian. Odd order gives A=A₊×A₋, the fixed and inverted subgroups. The same complement-conjugacy and counting proof gives |H∩A|≤|A₊|, with equality exactly when K mod A is a transversal, and then the projection is a loop homomorphism with kernel A₋. In fact the inequality is always strict. If A₋=1, equality would imply A≤H, contrary to core-freeness. If A₋≠1 and HA<G, equality gives a proper nontrivial kernel, contrary to simplicity. If HA=G, the abelian normal subgroup A is regular in the faithful action, so H∩A=1. Equality would imply A₊=1, hence K∩A=A; regularity gives |K|=|A|, so K=A and generation forces G=A, an associative contradiction. Thus

    |H∩A| < |C_A(τ)|                          (1)

for every nontrivial τ-stable abelian normal A. This is a necessary condition for simple nonassociative loops, not a proof of their nonexistence. In particular, the accumulated defect in any such normal layer never vanishes; taking a sum of minimal modules cannot force equality unless it contradicts simplicity or leaves the hypotheses. If τ inverts a nontrivial abelian τ-stable normal subgroup A, (1) is impossible. Applied to the inverted subgroup of Z(G), this proves τ fixes Z(G) pointwise.

Suppose V is an elementary abelian τ-stable minimal normal subgroup of G, so G acts irreducibly on V, and write R=G/C_G(V). If τ acts nontrivially on V, it has both eigenspaces nonzero by the anti-fixed obstruction. It induces an automorphism of R of order at most 2. If that automorphism were inner, it would be the identity, because Inn(R) has odd order. Then both τ-eigenspaces are R-invariant, contradicting irreducibility. Thus τ induces a **nontrivial outer involution** on R. In particular mixed V can occur only on a faithful irreducible representation of an odd-order group R admitting such an outer involution; if Aut(R) has odd order, τ fixes V pointwise. This is a concrete necessary representation-theoretic restriction, but outer involutions can occur, as the semilinear control above shows.

For the graph-pairing bookkeeping, let A=V⊕W be a τ-stable normal direct sum of two τ-stable elementary abelian G-modules over the same F_p. Set D=H∩A, D_V=D∩V, D_W=D∩W, and let P_V,P_W be the projections of D. All these are H-invariant. Goursat's lemma for subspaces gives a canonical H-module isomorphism

    P_V/D_V ≅ P_W/D_W,

with common dimension t=dim D−dim D_V−dim D_W. Writing a=dim C_V(τ), b=dim C_W(τ), d_V=dim D_V, d_W=dim D_W, counting in the earlier manuscript yields d_V≤a and d_W≤b, while (1) yields the strict graph bound

    t < (a−d_V)+(b−d_W).                     (2)

for any simple nonassociative Q (A nonzero). Thus any off-diagonal graph can recover at most the sum of the two individual defects minus one. A graph requires a common nonzero H-module subquotient of V and W; in particular, if those restricted H-modules have disjoint composition-factor sets, t=0. For completely reducible restrictions it suffices that they share no irreducible constituents. This is a necessary restriction on how radical layers can be coupled; it does not say they must couple, and nonsemisimple modular restrictions require the subquotient formulation.

For the known Q_{p,q} folder with odd p, the two minimal G-normal modules are interchanged by τ, rather than individually τ-stable. Their sum A=V×V has dim A₊=p while dim(H∩A)=p−1; the strict defect is one, so (1) permits the construction. This check uses only the stated C0003 folder data; it does not establish C0013's unproved absorption. The remaining substantive question is whether the outer-involution and strict graph constraints can be combined with the Bol transversality condition to eliminate a τ-stable mixed irreducible V, or to force a useful τ-paired layer. Neither follows from these observations alone.

At exact source `9d09b4c9fc854462d1888a528ffd5c7567d141ed`, [model reviewer identity omitted] accepted these further reductions, subject to restricting the final Q_{p,q} check to odd p as now stated. The review checked all equality cases including HA=G, the central and outer-involution consequences, and the H-subquotient argument, using the earlier reviewed quotient criterion and the stated C0003 data. No exhaustiveness or odd-envelope assertion for every Bol loop follows.

## Stabilizer displacement and repeated modules

The following bounded deductions have the scoped review below. Under the hypotheses of the strict abelian defect above, put $C=C_G(\tau)$. Then

$$H\cap\tau(H)=H\cap C<H.$$

Indeed, for $h\in H\cap\tau(H)$, the element $h^{-1}\tau(h)$ lies in $H$ and is inverted by $\tau$, hence belongs to $H\cap K=1$; the reverse inclusion is immediate. If $H\cap C=H$, the earlier identity $|H|=|C|$ gives $H=C$. By Feit–Thompson, the nontrivial odd-order group $G$ is solvable, so $A=Z(F(G))$ is nontrivial, characteristic and abelian. Then $H\cap A=C_A(\tau)$ contradicts the strict defect. In particular $\tau(H)\ne H$; this does not imply that minimal normal modules occur in $\tau$-paired copies. The argument avoids Feit–Thompson if a nontrivial $\tau$-stable abelian normal subgroup is assumed directly.

For the trace exact-factorization ansatz in C0013 [context outside this selected packet: `../claims/C0013.md`], repeated isomorphic modules give a separate obstruction. Let $p,q$ be primes with $\operatorname{ord}_q(p)=p$, $F=\mathbb F_{p^p}$, and $X=M\rtimes(C_q\rtimes\langle\phi\rangle)$, where $M=\bigoplus_{i=1}^k M_{r_i}$, the $C_q$-generator acts on $M_{r_i}=F$ as multiplication by $\zeta^{r_i}$, and $\phi(z)=z^p$. Take $Y_1=C_q\rtimes\langle\phi\rangle$ and

$$Y_0=\{(m_1,\ldots,m_k;0,j):\sum_i c_i\operatorname{Tr}_{F/\mathbb F_p}(m_i)=j\},\qquad c_i\in\mathbb F_p.$$

If $r_j\equiv p^s r_i\pmod q$ for distinct indices, choose $(a,b)\ne(0,0)$ with $c_i a+c_j b=0$. The subgroup $D\cong F^+$ supported on those two coordinates as $(az,bz^{p^s})$ is normal in $X$ and lies in $Y_0$: Frobenius identifies the modules and preserves trace. Thus $Y_0$ is not core-free. Moreover $Y_0,Y_1$ form an exact factorization, as $|Y_0|=|M|$ and $Y_0\cap Y_1=1$; their images give an exact factorization of $X/D$. The natural quotient induces a surjective homomorphism between the associated ambient exact-factorization loops with kernel $D$, which is nontrivial and proper. Hence the original loop is not simple. This applies also when $p=2$ and does not establish C0013's absorption or the exhaustiveness of the distinct-orbit family.


GPT-6.1 Terra reviewer [model reviewer identity omitted] accepted this final section at exact source `698ce5f6d50e7186f205a63f4a2c413145775915`, relying on the earlier section reviewed at `9d09b4c9fc854462d1888a528ffd5c7567d141ed`. The review covers the stabilizer identity and strict displacement, the stated Feit–Thompson/solvable-group input, and the repeated-module normal graph and proper quotient-loop kernel, including p=2 and zero coefficients. It does not establish C0013 absorption or distinct-orbit exhaustiveness. No computation or formal verification is used.

## Strict defect for every proper invariant normal subgroup

This extension has the scoped review below. Let (G,H,K) be a finite faithful generating left Bol folder of a simple nonassociative loop, with |G| odd. Assume τ is an involutory automorphism inverting K, and τK is G-conjugacy-invariant. Put C=C_G(τ). As in odd-folder-radicals.md, coprime complement conjugacy gives K={g:τ(g)=g⁻¹}, |K|=[G:C], and |H|=|C|.

For every nontrivial proper τ-stable normal subgroup N◁G, not necessarily abelian,

    |H∩N| < |C_N(τ)|.                                        (1)

Indeed, τ induces an automorphism of order dividing two on G/N. Complement conjugacy in N⋊⟨τ⟩ shows C_G(τ) maps onto C_{G/N}(τ), so |C_{G/N}(τ)|=|C|/|C_N(τ)|. It also shows the image Kbar of K is the full inverted subset of G/N: the involutions τKbar form the full conjugacy class of τ and every conjugator lifts. Thus

 |Kbar|/[G:HN] = |C_N(τ)|/|H∩N|.

The image Kbar covers G/HN, making the ratio at least 1. Equality is equivalent to transversality, in which case the quotient triple (G/N,HN/N,Kbar) is a Bol folder and K→Kbar a surjective loop homomorphism with kernel K∩N. If K∩N is nontrivial, simplicity makes the kernel the entire loop; then K⊆N and generation forces N=G, contrary to properness. If K∩N=1, the full inverted subset of N is trivial. Odd-order complement conjugacy then gives |N:C_N(τ)|=1, so C_N(τ)=N; equality would give N≤H, contradicting core_G(H)=1. Thus the inequality is strict.

A second conclusion holds independently of the strict inequality: every τ-stable normal subgroup N on which τ acts trivially is central. For n∈N and k∈K, the element knk⁻¹∈N is τ-fixed, whereas applying τ gives k⁻¹nk. Thus k² centralizes n. Since G has odd order, k∈⟨k²⟩, so k centralizes n; K generates G. The reviewed abelian-radical result says τ fixes Z(G) pointwise, so the τ-fixed normal subgroups are precisely the central subgroups. This is a structural necessary condition; it neither implies that the loop has odd G from its order nor classifies the loops or proves an exact factorization.

GPT-6.1 Terra reviewer [model reviewer identity omitted] accepted the final general normal-subgroup section at exact source `95f226ac6c02b0153f3c226d823518e0891c1f1d`, relying on the prior reviewed odd-folder results. The review checked complement conjugacy for arbitrary odd N, centralizer surjectivity, the full inverted image, and transversality to every conjugate of HN/N (by projection of the original conjugate transversals and equality of sizes). It checked both simplicity-kernel extremes and the fixed-normal-if-and-only-if-central conclusion. The odd-order G hypothesis remains explicit; no odd-envelope theorem for all odd-order loops or classification follows. No computation or formal verification was performed.

## Source application to odd-order loops

**Scoped independent source review recorded below.** Let Q be any finite left Bol loop of odd order and take its canonical faithful generating envelope G=LMlt(Q), H the identity stabilizer, and K the left translations. The set K generates G and is a twisted subgroup. By left power-alternativity and Foguel–Kinyon–Phillips, [arXiv:math/0208231v2](https://arxiv.org/abs/math/0208231v2), Proposition 6.1, every element of K has odd order, so K is uniquely 2-divisible. Their Theorem 4.14 therefore gives |G| odd; alternatively, Theorem 6.7 applies with π the prime divisors of |Q|. This source application does not use their later Lemma 6.22 or its stabilizer argument. Published-version theorem numbering has not been verified.

Thus the earlier odd-G results apply to the canonical envelope of a simple nonassociative odd-order left Bol loop when their other stated hypotheses are satisfied, including the involution, conjugacy-invariance, and strict-defect hypotheses where invoked. This removes no other assumption and gives no classification.

[model reviewer identity omitted] accepted this source application at exact source `ab4059e6a9b8d5876e2bffa993bb98e7dac69025` after directly checking FKP v2 Example 5.1, Proposition 6.1 and Theorem 4.14, including its general radical-quotient case, and the independent Theorem 6.7 route. No Bruck or radical-free hypothesis is needed; the later Lemma 6.22 is not used. This applies to the canonical faithful generated envelope and retains the other hypotheses of the earlier results. Published-version numbering remains unverified, and no unrestricted classification follows.

## No proper normal Hall subgroup

**Scoped independent review below.** Under the canonical odd-order simple nonassociative Bol-loop hypotheses just applied, G has no nontrivial proper normal Hall subgroup. This uses the general strict-defect section reviewed at `95f226ac6c02b0153f3c226d823518e0891c1f1d` and the odd-envelope source application reviewed at `ab4059e6a9b8d5876e2bffa993bb98e7dac69025`, retaining their folder/inversion inputs.

Suppose N is a nontrivial proper normal Hall π-subgroup of G. Every π-subgroup maps trivially to the π′-group G/N and is contained in N. Thus N is characteristic, in particular τ-stable. Both H∩N and C_G(τ)∩N are π-groups; their respective quotients in H and C_G(τ) embed in G/N and have π′-order. Consequently

    |H∩N|=|H|_π=|C_G(τ)|_π=|C_N(τ)|,

contradicting the strict defect. This elementary Hall argument requires no additional coprime lifting theorem.

In particular no proper normal Sylow subgroup can occur. If G is monolithic with elementary abelian unique minimal normal subgroup M of characteristic p and M<G, then p divides |G/M|. Otherwise M would be normal Hall. The case M=G would make the faithful generated folder associative. This excludes the preceding Frobenius mixed-eigenspace control as a simple envelope, but does not exclude monolithic groups with p dividing |G/M|, force τ-paired minimal modules, or establish an exact-factorization witness. No new computation is used.

GPT-6.1 Terra reviewer [model reviewer identity omitted] accepted the no-normal-Hall section at exact source `e2e4609612cf6de99be9d2456c339b18d4a04173`, conditional on the pinned strict-defect and odd-envelope source inputs. The review checked characteristicity, the equal π-parts, the strict-defect contradiction and the monolithic consequence, including the associative case M=G. It neither forces paired minimal modules nor classifies the remaining groups; no computation or formal verification was used.


## Proposed mixed-module stabilizer obstruction

**Scoped independent review below.** The strict-defect input is the result reviewed at `95f226ac6c02b0153f3c226d823518e0891c1f1d` above, and oddness of the canonical envelope uses the source application reviewed at `ab4059e6a9b8d5876e2bffa993bb98e7dac69025` above. Let p be an odd prime and q a prime with ord_q(p)=p. Put T=C_q×C_q and A=T⋊⟨t⟩, where t has order p and acts on the two q-coordinates by multiplication by p and p^−1. Let α interchange the two coordinates and invert t. Let V be a nonzero finite elementary abelian p-group with an F_p A-module structure and an involution σ satisfying σ(a v)=α(a)σ(v). Assume:
  (i) each of the two coordinate C_q subgroups acts fixed-point-freely on V;
  (ii) d_+=dim_Fp C_V(σ) is divisible by p.
Use the semidirect convention $(v,a)(w,b)=(v+a w,ab)$, set $G=V\rtimes A$, and define $\tau(v,a)=(\sigma v,\alpha a)$. Then G with this involution cannot be the canonical envelope and inverting automorphism of a finite simple nonassociative odd-order Bol loop.

Proof. If it were, the reviewed odd-envelope results would give |H|=|C_G(τ)| and strict defect |H∩V|<|C_V(τ)|, where H is the identity stabilizer. Here C_A(α) is the diagonal C_q: an α-fixed element has trivial t-coordinate, and diagonal q-coordinates. Thus |H|=q p^{d_+}. Since H∩V is a p-group and H/(H∩V) embeds in A, whose p-part is p, strict defect forces dim(H∩V)=d_+−1 and Hbar=HV/V of order pq. The q-part of $|\bar H|$ is q, and the projection $\bar H\to A/T$ is onto because $|\bar H|=pq$. Thus $\bar H\cap T$ is a line of order q, normalized by some $u t^j$ with $u\in T$ and $j\ne0$ modulo p. As $T$ is abelian, conjugation by $u t^j$ on $T$ is the same as conjugation by $t^j$; its eigenvalues $p^j$ and $p^{-j}$ are distinct modulo q. Hence the line is one of the two coordinate axes. Every nontrivial irreducible F_p C_q-module has dimension ord_q(p)=p; hypothesis (i) implies V has no trivial constituent on this axis, so every invariant subspace has dimension divisible by p. But H∩V is Hbar-invariant of dimension d_+−1, a contradiction.

This is a group/module exclusion, not an assertion that the displayed groups admit any Bol folder or a proof that all odd simple envelopes admit an exact-factorization witness. The cited inputs are FKP, arXiv:math/0208231v2, Proposition 6.1 and Theorem 4.14 (oddness of G), C0007 proof Theorem 1.1(1) (canonical inverting τ), and the strict-defect and full-inverted-set results in odd-folder-radicals.md. This section and its following control have the scoped independent review below; no formal verification is claimed.

## A monolithic irreducible mixed-module test for every p,q

Let F=F_{p^p} and ζ∈F have order q. Let V=⊕_{j∈F_p} F e_j, viewed over F_p. Define a,b∈C_q² and t by
  a e_j=ζ^{p^j}e_j,   b e_j=ζ^{p^{−j}}e_j,   t e_j=e_{j−1},
and σ F-linearly by σ(e_j)=e_{−j}. Then σ interchanges a,b and conjugates t to t^−1. Both q-axes act fixed-point-freely, and dim_Fp C_V(σ)=p(p+1)/2, divisible by p. The preceding result excludes a simple folder with this (G,τ).

V is an irreducible F_p A-module: its q²-character on each F-line is (p^j,p^−j); two of their Frobenius orbits coincide only if 2j=2k mod p, so each F-line is a distinct irreducible T-module and t permutes these p constituents transitively. The A-action is faithful: the j=0,1 characters separate the two q-coordinates since p and p^−1 are distinct modulo q, and a nontrivial power of t permutes the F-lines. Hence G=V⋊A is monolithic with unique minimal normal subgroup V: every normal subgroup disjoint from V centralizes V, but C_G(V)=V. Its center is trivial, its minimal normal V is not Hall because p divides |A|, and σ has both nonzero eigenspaces.

Moreover G_ab≅C_p and τ induces inversion on it: [A,V]=V and A′=C_q². The full τ-inverted set generates G. Indeed let L be its normal closure; every g^−1τ(g) is τ-inverted, so τ acts trivially on G/L. But τ induces inversion on the abelianization of every quotient of G, while any nontrivial finite solvable quotient of G has nontrivial odd-order abelianization. Thus G/L=1. In fact the full inverted set is the set of $\tau$-commutators $g^{-1}\tau(g)$: inclusion in the inverted set is immediate, while an inverted $k$ equals $g^{-1}\tau(g)$ for $g=k^{-1/2}$ because $G$ has odd order. The subgroup generated by these commutators is normal: $(g^{-1}\tau(g))^h=((gh)^{-1}\tau(gh))(h^{-1}\tau(h))^{-1}$. Thus the full inverted set itself generates $G$.

Thus mixed irreducibility, monolithicity, odd solvability, inversion on abelianization, full inverted-set generation, and p dividing |G/V| coexist; they alone do not force a paired minimal normal. The exclusion above uses the additional simple-folder stabilizer and strict-defect constraints.

GPT-6.1 Terra reviewer [model reviewer identity omitted] accepted the mixed-module obstruction and irreducible monolithic control at exact source `9009bb98c97148e7cf250344f714528b1620b0a9`, conditional on the pinned strict-defect and odd-envelope inputs. The review checked the fixed subgroup, projected stabilizer order, invariant q-axis and modular dimension contradiction, then the explicit module’s irreducibility, faithful action, mixed eigenspaces, monolithicity and full inverted-set generation. It does not assert a Bol folder for the control or an exhaustive description of odd envelopes. No computation or formal verification was used.


## Proposed modular defect congruence

**Deductions with scoped independent review below.** No formal verification is claimed. Let Q be a finite simple nonassociative odd-order left Bol loop, G=LMlt(Q), H its identity stabilizer, τ the canonical inverting involution, and V a nonzero proper τ-stable elementary abelian normal p-subgroup. Put A=G/V, let α be the induced involution, and define
 c=dim_Fp C_V(τ),  m=v_p([A:C_A(α)]),  J=HV/V.
Assume some prime q≠p divides |C_A(α)| and every subgroup of A of order q acts fixed-point-freely on V. Put r=ord_q(p). Then there is an integer δ with
  1≤δ≤m   and   δ≡c (mod r).
In particular, no such canonical envelope exists if [1,m] contains no integer congruent to c modulo r; e.g. if r divides c and m<r.

Proof. Coprime complement conjugacy gives a surjection C_G(τ)→C_A(α), whose kernel is C_V(τ); the full-inverted-set theorem yields |H|=|C_G(τ)|. By the reviewed strict-defect theorem, H∩V has order p^w with w<c. Therefore
 |J|=|H|/|H∩V| = p^(c−w)|C_A(α)|.
Set δ=c−w≥1. Since J≤A, δ≤v_p([A:C_A(α)])=m. The prime q divides |J|, so J has a subgroup B of order q. It acts on the F_p-space V (the action of A is well-defined because V is abelian), with no nonzero fixed vector. Maschke's theorem for B implies every B-invariant subspace is a sum of nontrivial irreducibles, each of dimension r=ord_q(p). Thus r divides dim(H∩V)=w, yielding δ≡c mod r. No split extension, irreducibility of V, solvability of J, or monolithic condition is assumed.

Source inputs: Foguel–Kinyon–Phillips arXiv:math/0208231v2, Proposition 6.1 and Theorem 4.14 give odd G; C0007 proof Theorem 1.1(1) gives τ; odd-folder-radicals.md gives full inverted set, centralizer lifting, and strict defect for proper τ-stable normal subgroups (reviewed at 95f226ac6c02b0153f3c226d823518e0891c1f1d; FKP source application reviewed ab4059e6a9b8d5876e2bffa993bb98e7dac69025). Standard coprime representation facts are used as shown.

## Uniform higher-p-length monolithic test

Let p be an odd prime. Take n=p^k for k≥1, and choose a prime q with ord_q(p)=n, and let F=F_{p^n}, ζ∈F of order q. Set A=(Cq×Cq)⋊Cn with t acting on the two q axes by p and p^−1, and α swapping the axes and inverting t. Let V=⊕_{j mod n} F e_j, with
 a e_j=ζ^{p^j}e_j,  b e_j=ζ^{p^(−j)}e_j,  t e_j=e_{j−1},  σ(e_j)=e_{−j},
where σ is F-linear. Then σ implements α; C_A(α) is diagonal Cq, and σ has c=n(n+1)/2 fixed F_p-dimensions, so n|c, while m=v_p(n)=k<n=r. Every order-q subgroup of A is a line in Cq². However the diagonal-type lines may have nonzero fixed vectors on V: their character ζ^{u p^j+v p^(−j)} can be trivial. Hence the global fixed-point-free hypothesis of the lemma is not automatic and is not asserted for this example.

A separate forced-axis argument excludes the explicit model. If it were a simple canonical envelope, strict defect and the centralizer count would give $|J|=q p^\delta$ with $1\leq\delta\leq k$. Thus $J\cap C_q^2$ has order $q$, and the image of $J$ in $C_n$ is nontrivial. An element $u t^j\in J$ with $u\in C_q^2$ and $j\not\equiv0\pmod n$ normalizes this q-line. Conjugation by $u t^j$ acts on $C_q^2$ as $t^j$, whose eigenvalues $p^j$ and $p^{-j}$ are distinct because $n$ is odd and $\operatorname{ord}_q(p)=n$. The q-line is therefore a coordinate axis. Both axes act fixed-point-freely on V, so the invariant subspace $H\cap V$ has dimension divisible by $n$. Consequently $\delta\equiv c\equiv0\pmod n$, impossible for $1\leq\delta\leq k<n$. This argument does not use the generic lemma’s global fixed-point-free hypothesis.

The Fp A-module V is irreducible: each F-line has q²-character (p^j,p^−j); two Frobenius orbits coincide only if 2(j−h)=0 mod n, so they are distinct, and t permutes them transitively. A acts faithfully, G=V⋊A is monolithic with unique minimal normal V, and τ(v,a)=(σv,αa) has mixed eigenspaces and induces inversion on G_ab≅Cn. All τ-inverted elements generate G: their generated subgroup is the normal subgroup generated by τ-commutators, τ is trivial on the quotient, but acts by inversion on the abelianization of every quotient; a nontrivial odd solvable quotient has nontrivial abelianization. Thus the obstruction uses simple-folder stabilizers, not merely group structure or τ-generation.

For every odd prime p and k≥1 a suitable q exists by the elementary argument below. Thus this excludes an infinite sequence of concrete mixed, monolithic, unbounded p-index quotient models. It does not exclude arbitrary monolithic groups or prove any exact factorization.

GPT-6.1 Terra reviewer [model reviewer identity omitted] accepted the modular defect congruence and higher-p-length model at exact source `457858c2fe7b8865a5e7682173361aaec551537c`, conditional on the reviewed strict-defect and odd-envelope inputs. The review checked coprime centralizer lifting, modular dimensions without splitness, the separate forced-axis argument where the generic fixed-free hypothesis fails, irreducibility, faithfulness, mixed eigenspaces, monolithicity and full inverted-set generation. The reviewer requested a justification of the asserted infinite supply of primes; the following new argument was supplied afterward and was not present at that source revision. No computation or formal verification was used.

**Prime existence, with scoped independent review.** Put N=p^(k−1) and S=Σ_{i=0}^{p−1}p^{iN}>1. Then S≡1 (mod p), so any prime divisor q of S differs from p. Since (p^N−1)S=p^{p^k}−1, the order of p modulo q divides p^k. If it were a proper divisor, it would divide N, making S≡p (mod q) and forcing q=p, a contradiction. Thus every prime divisor q of S has order exactly p^k. GPT-6.1 Terra reviewer [model reviewer identity omitted] subsequently accepted this committed elementary argument at exact source `e684b2ef774d331b786e72b49df5d9d812362f25`. This discharges the prime-existence qualification on the preceding review without invoking an external primitive-prime-divisor theorem.

## Candidate simplicity criterion using τ-stable normal subgroups

**Lemma with scoped independent reviews below.** Let (G,H,K) be a finite faithful generating left Bol folder, with G of odd order and an automorphism τ satisfying τ(k)=k⁻¹ for every k∈K. Assume the full-inverted-set and centralizer-ratio conclusions of the earlier odd-folder argument. Then its loop Q is simple if and only if

    |H∩N| < |C_N(τ)|

for every nontrivial proper τ-stable normal subgroup N◁G. This criterion includes associative simple loops; it does not assert that the kernel of every loop quotient is τ-stable.

Proof. The reviewed ratio argument at `95f226ac6c02b0153f3c226d823518e0891c1f1d` gives, for each such N,

    |KN/N| / [G:HN] = |C_N(τ)| / |H∩N| ≥ 1,

and equality exactly when the projected section is a transversal. If equality holds, C0001's quotient criterion gives a loop homomorphism with kernel K∩N. This kernel is nontrivial: core_G(H)=1 prevents nontrivial N from lying in H, while transversality gives |K∩N|=[N:H∩N]>1. If HN<G the quotient is nontrivial, so Q is not simple. If HN=G, equality forces |KN/N|=1, hence K⊆N; generation would give N=G, contrary to properness. Thus simplicity implies strict inequality.

Conversely, suppose Q is not simple. Extend a nontrivial proper normal subloop to a maximal proper normal subloop P, and let S=Q/P. Then S is a nontrivial simple left Bol loop, and the natural epimorphism

    ρ:G → LMlt(S)

sends each left translation to the corresponding quotient translation. Its kernel N is normal and nontrivial: if 1≠p∈P, then L_p∈N and L_p≠1 by faithfulness. It is proper because LMlt(S) is nontrivial. The preimage under ρ of the identity stabilizer in LMlt(S) is HN: if g sends the identity of Q into p∈P, then L_p∈N and L_p⁻¹g∈H. Hence [G:HN]=|S|>1.

If S is nonassociative, C0001's nucleus-normality and simplicity give trivial left nucleus, so the invoked part of C0007 provides an automorphism τ' of LMlt(S) inverting its translations. If S is associative, it is a simple group of odd order and is solvable because LMlt(S) is a quotient of the odd-order solvable group G; hence S is cyclic of prime order, and inversion is an automorphism τ'. In either case ρτ=τ'ρ on the generating set K, so N is τ-stable. C0001's quotient criterion yields |KN/N|=[G:HN]. The displayed ratio then gives |H∩N|=|C_N(τ)|, contradicting strict inequality. ∎

This equivalence uses a maximal proper normal subloop so that the quotient is simple; it gives no τ-stability assertion for kernels of arbitrary quotients. It does not prove the intrinsic exact-factorization witness or supply an unrestricted classification. GPT-6.1 Terra reviewers [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted this equivalence at exact source `65a3e58df517df59656ab948ac9d122208f62c4a`, conditional on C0001, C0007, the reviewed odd-group full-inverted-set and centralizer-ratio results, and odd-order solvability. Both checked the necessity argument, nontrivial proper kernel of the action on the maximal simple quotient, the equality of its stabilizer preimage with HN, inversion in the nonassociative and associative quotient cases, and τ-stability from agreement on the generating translations. Neither review asserts τ-stability for kernels of arbitrary quotients, an exact-factorization witness or a classification. No computation or formal verification was used.


## Proposed irreducible rank-two quotient obstruction

**Section with scoped independent review below.** No formal verification is claimed. Let p,q be distinct odd primes, n=p^k>1, and choose ℓ∈F_q^× of order n. Set T=C_q×C_q and A=T⋊⟨t⟩, |t|=n, where t acts on T by (ℓ,ℓ^−1). Let α swap the two coordinates of T and invert t. Let 1→V→G→A→1 be any finite group extension, where V is a faithful irreducible F_p A-module and elementary abelian, and let τ be an involution of G stabilizing V and inducing α on A. Then (G,τ) cannot be the canonical envelope and canonical inverting involution of a finite simple nonassociative odd-order Bol loop.

Proof. The fixed subgroup C_A(α) is diagonal C_q. If the canonical folder existed, the reviewed strict-defect and coprime fixed-point lifting results would imply |H|=q p^c with c=dim_Fp C_V(τ), and, writing w=dim_Fp(H∩V), δ=c−w, J=HV/V,
 |J|=q p^δ,   1≤δ≤k.
Hence J∩T is a line of order q, normalized by some ut^j∈J with u∈T and j nonzero modulo n. Its conjugation action on T has distinct eigenvalues ℓ^j and ℓ^−j, because n is odd and ℓ^j≠1. So J∩T is an axis. Faithfulness and irreducibility imply that each q-axis acts without fixed points: its fixed subspace is A-invariant because the axis is normal in A; if nonzero it equals V, contradicting faithfulness. Let r=ord_q(p). Every nontrivial irreducible F_p C_q-module has dimension r. Hence r|w, and δ≡c (mod r).

It remains to determine c modulo r. Since q≠p, V|_T is semisimple. Over an algebraic closure choose a nontrivial T-character λ=(u,v). Faithfulness implies both u,v are nonzero: if one were zero, its entire A-orbit and Frobenius orbit would still vanish on that axis, which would act trivially on all V by irreducibility. If t^jλ=p^hλ, then ℓ^j=p^h=ℓ^−j, so ℓ^{2j}=1. As n is odd, j=0 mod n and p^h=1 mod q. Thus the n t-conjugates of the F_p-irreducible T-summand are distinct, each of dimension r. Irreducibility of V makes V their direct sum, with no multiplicity: the inertia subgroup is T, so modular Clifford theory gives V=Ind_T^A(U) for that r-dimensional simple T-module U. Equivalently, the direct sum of the n distinct t-translates of any one irreducible T-submodule is a nonzero A-submodule, hence all of V.

Since τ implements α and V is irreducible, swapping λ's coordinates is p^h t^jλ for some h,j. Applying swap twice shows p^{2h}=1 mod q (the t-weights cancel), hence h=0 or, if r is even, h=r/2 modulo r. The involution permutes the n distinct F_p T-summands as a reflection, with one fixed summand and (n−1)/2 pairs. Each pair contributes r to c. On the fixed summand, τ is semilinear over F_{p^r}, with field part p^h. If h=0 it is F_{p^r}-linear and squares to 1, so its scalar is ±1 and it fixes either 0 or r F_p dimensions. If h=r/2, write its action on the fixed summand as $x\mapsto b\overline{x}$, where the bar is the nontrivial automorphism of $\mathbb F_{p^r}/\mathbb F_{p^{r/2}}$. Its square being the identity gives $b\overline b=1$. Since the multiplicative group of the finite field is cyclic, every norm-one element has the form $a/\overline a$; rescaling by $a$ conjugates the involution to the bar map. Its fixed space is therefore $a\mathbb F_{p^{r/2}}$ and has exactly $r/2$ dimensions over $\mathbb F_p$. Consequently
 c≡0 (mod r), or, when r is even, c≡r/2 (mod r).

Since ℓ has order n, n divides q−1. As q is odd, q≥2n+1=2p^k+1. Also q divides p^r−1, so r>k. In the second case p^{r/2}≡−1 mod q, so q divides p^{r/2}+1; that quotient is even, yielding p^{r/2}+1≥2q and hence r/2>k. Therefore neither residue class c mod r has a representative δ in [1,k], contradicting δ≡c mod r.

This proves a bounded nonsplit extension exclusion for faithful irreducible modules; it does not imply all odd simple envelopes have a quotient A of this form, all such groups are monolithic, or exact-factorization exhaustiveness. Canonical oddness and strict defect use FKP arXiv:math/0208231v2, Proposition 6.1 and Theorem 4.14, and the general normal-subgroup section above reviewed at `95f226ac6c02b0153f3c226d823518e0891c1f1d`. The FKP source application was independently reviewed at `ab4059e6a9b8d5876e2bffa993bb98e7dac69025`. Induced module claim is proved by transitivity in the text; fixed-space descent can be proved elementarily by choosing a nonzero fixed vector via finite-field Hilbert 90. No computation is claimed for this section.


GPT-6.1 Terra reviewer [model reviewer identity omitted] independently accepted the irreducible rank-two quotient obstruction at exact source `0e6e9e245ae75d4d814b6ae0a6f27a2d95174ad2`, conditional on the pinned odd-envelope and strict-defect inputs. The review checked the forced q-axis, the faithful irreducible module decomposition and multiplicity one, the Frobenius reflection and fixed-space alternatives, the inequalities excluding every allowed defect, and the fact that the extension need not split. It does not assert exhaustiveness for odd envelopes or an exact-factorization witness.

## Proposed fixed stabilizer intersection and eigenspace geometry

These further deductions have the **scoped independent review below**. Use the canonical faithful generating folder of a finite simple nonassociative odd-order left Bol loop, with the oddness, full-inverted-set and strict-defect inputs pinned above. The result reviewed at `95f226ac6c02b0153f3c226d823518e0891c1f1d` says τ fixes Z(G) pointwise. Then

    N_G(K)=C_G(τ),   H∩τ(H)=LInn(Q)∩Aut(Q),

where the final intersection is inside Sym(Q). A τ-fixed element normalizes the full inverted set K. Conversely, if g normalizes K, comparison of τ(gkg⁻¹) with (gkg⁻¹)⁻¹ for every k∈K shows τ(g)⁻¹g∈Z(G). This element is τ-inverted and τ-fixed, hence has order at most two and is trivial in odd G. Thus N_G(K)=C_G(τ). A permutation h∈H fixes 1 and is a loop automorphism exactly when it normalizes the set of left translations, proving the second equality via the already reviewed H∩τ(H)=C_H(τ).

In particular coprimality of |H| and |Aut(Q)| suffices for trivial intersection, but is not necessary. If a nontrivial p-subgroup of this intersection acts and p divides |Q|, its fixed-point set is a proper nontrivial subloop: fixed points are closed under products and both divisions, the faithful nontrivial action makes the set proper, and orbit counting makes its cardinality divisible by p. Such a subloop need not be normal, so this gives no contradiction to simplicity. Oddness, generation and non-Bruckness alone cannot force trivial intersection: take the direct product of the nonsimple F_{3^6}⋊C₇ Bruck folder above and the known Q₁₀₅₃ folder. The first factor supplies a nontrivial τ-fixed stabilizer, and the second makes the product non-Bruck; the product is nonsimple. This is a boundary control, not a counterexample to a proposed simple-loop statement.

Now let V be a nonzero τ-stable elementary abelian normal p-subgroup, put σ=τ|V, V=V₊⊕V₋, W=H∩V, and R=G/C_G(V)≤GL(V). Write a=dim V₊, b=dim V₋, w=dim W and δ=a−w. Every R-conjugate of V₋ is disjoint from W. Indeed, for λ a G-conjugate of τ̂, every vector x in its negative eigenspace makes λ and λx involutions in τ̂G, hence members of the full marked class Λ; thus x∈Λ², which meets H trivially.

There is also a limitation on this avoidance test. For every odd-order linear group R normalized by an involution σ, the R-orbit unions of the projective spaces P(V₊) and P(V₋) are disjoint. If r u₊=c u₋ for r∈R, c∈F_p^× and nonzero eigenvectors, then r⁻¹(σrσ⁻¹)∈R sends u₊ to −u₊, impossible for an odd-order linear transformation. Therefore a projectively transitive odd R admits no mixed σ, but **every subspace W⊆V₊ already satisfies the entire avoidance test**. Avoidance alone cannot exclude a mixed irreducible minimal normal subgroup; compatibility with the projected stabilizer and strict defect is essential.

Finally B=H∩τ(H) contains W∩V₊, giving

    |B|≥p^{max(0,w−b)}=p^{max(0,a−b−δ)}.

Centralizer lifting and |H|=|C_G(τ)| give 1≤δ≤v_p([G/V:C_{G/V}(τ)]) by the previously reviewed quotient count. Thus B=1 would require δ≥a−b. If a−b exceeds that index valuation, every simple folder with the prescribed layer would have B≠1. No such folder is constructed here, and neither universal triviality of B nor a monolithic-envelope exclusion is asserted. No computation is used.


GPT-6.1 Terra reviewer [model reviewer identity omitted] independently accepted the fixed-stabilizer and eigenspace-geometry section at exact source `8ad35e2dbed5179f70be146d73b61ae80bde5555`, conditional on the pinned odd-envelope, center, strict-defect and known-control inputs. The review checked both normalizer identities, the fixed-subloop argument and nonsimple product control, disjoint projective orbit unions and automatic avoidance, and the stabilizer-size/valuation bounds. It establishes neither a simple-folder example nor universal triviality of the intersection or a monolithic-envelope exclusion; no computation or formal verification was used.


## Proposed stabilizer displacement cocycle

**Section with scoped independent review below.** Source context: C0001 faithful-folder and transversal correspondence, C0007 canonical inverting involution, C0010 odd frontier, and odd-folder-radicals.md strict-defect/full-inverted-set inputs (reviewed at 95f226ac6c02b0153f3c226d823518e0891c1f1d; FKP oddness source application at ab4059e6a9b8d5876e2bffa993bb98e7dac69025). No universal exact-factorization assertion is claimed.

Let (G,H,K) be the canonical folder of a finite simple nonassociative odd-order Bol loop, τ its inverting involution, and V a nonzero τ-stable elementary abelian normal p-subgroup. Put σ=τ|V, V=V+⊕V−, W=H∩V, A=G/V, J=HV/V, J0=J∩C_A(τbar), B=H∩τ(H)=C_H(τ), D=W∩V+. Write a=dim V+, b=dim V−, w=dim W, d=dim D.

The folder condition gives W∩V−=0, so projection to V+ identifies W with the graph of a linear map f:U→V− for a w-dimensional U≤V+. We have D=ker f, W∩σW=D, and W+σW=U⊕im f. The subgroup B normalizes H, V and τ, hence acts on both eigenspaces and preserves the graph; U and im f are B-stable and f is B-equivariant. These are genuine subgroup-closure constraints, but a graph with nonzero kernel can still satisfy all anti-eigenspace avoidance conditions.

Define E=V−/(1−σ)W, of dimension b−w+d. The subspace (1−σ)W is J0-invariant: J preserves W, while J0 commutes with σ in its action on V. There is a well-defined crossed homomorphism c:J0→E: for j∈J0 choose h∈H with hV=j and set
 c(j)=τ(h)h^−1 mod (1−σ)W.
The numerator lies in V−, since τ(j)=j and τ(τ(h)h^−1)=(τ(h)h^−1)^−1. Replacing h by u h with u∈W changes it by (σ−1)u. Multiplication gives c(jk)=c(j)+j·c(k).

The lift of j can be adjusted by an element of W to be τ-fixed iff c(j)=0. Thus there is an exact sequence
  1→D→B→ker c→1.
Here ker c is a subgroup, and c(x)=c(y) iff y^−1 x∈ker c, so the fibers are the left cosets y ker c; in particular, c embeds that set of left cosets into E. No normality of ker c is asserted. Consequently
  |B|=p^d|ker c|,   [J0:ker c]≤p^{b−w+d}.
In particular, if B=1 then d=0 and c is injective as a set, so |J0|≤p^{b−w}. More generally |J0|>p^{b−w+d} forces ker c≠1 and B≠1. This is a quotient-cocycle obstruction to trivial fixed stabilizer that uses H's subgroup closure and works without a splitting of G over V. It remains conditional: no simple folder is constructed for which the inequality holds.

A complementary exact identity, derived by the collaborating agent [model reviewer identity omitted], is
  K∩Hτ(H)={h τ(h)^−1:h∈H},  |K∩Hτ(H)|=[H:B].
Indeed, if hτ(j)∈K then τ(jh)=(jh)^−1; since jh∈H and K is the full inverted set, jh∈H∩K=1. Conversely hτ(h)^−1∈K. Two such values agree exactly when their h arguments differ by an element of C_H(τ)=B. This identity uses the product set Hτ(H), not a claim that it is a subgroup.

Failed route/boundary: avoidance of all conjugate V− alone cannot force B=1 or a paired minimal layer, since every subspace of V+ automatically avoids them for an odd-order action. The non-Bruck product control in odd-folder-radicals has B≠1 but is nonsimple. The cocycle obstruction narrows the remaining issue to its realizability under the complete folder and simple normal-subgroup conditions; it does not prove or refute universal B=1.

A qualitative consequence: let T=C_{J0}(E). The restriction c|T:T→E^+ is an ordinary homomorphism. Thus every p′-element of T and the derived subgroup T′ lie in ker c. If B=1, T must be elementary abelian of exponent p and embeds into E. In particular, any nonidentity p′-element of J0 acting trivially on E forces B≠1. This is independent of the cardinality test, and still conditional on the existence of the folder.

## A paired-quotient sufficient condition for B=1

The following has the scoped review below and does not assume an exact-factorization witness or a split extension. Let V=V1×V2 be a τ-stable normal subgroup, with V1,V2 interchanged by τ and V1∩V2=1. Suppose H∩V≤V1, and identify (G/V,τbar) with (A,α), where
 A=(D×D)⋊⟨t⟩,    t(x,y)t^−1=(ρ(x),ρ^−1(y)),    α(x,y,t^j)=(y,x,t^−j),
D is any finite group, ⟨t⟩ has odd order and ρ has order dividing |t|. If J=HV/V≤(1×D)⋊⟨t⟩, then H∩τ(H)=1. Indeed, B=H∩τ(H)=C_H(τ) maps to J∩C_A(α). Since |t| is odd, C_A(α)=diag(D), and this intersects (1×D)⋊⟨t⟩ trivially. Hence B≤V. As B≤H, B≤V1, while τ fixes B pointwise and maps V1 to V2; V1∩V2=1 gives B=1. This criterion does not require V to be elementary abelian or the loop to arise from any exact factorization. It is a sufficient condition for B=1, not an existence or exhaustive-structure theorem.

For the Q_{p,q} control, take V=V1×V2 the two normal field modules, D=C_q, t=(φ,φ^−1), W=ker Tr×0, and J=(1×C_q)⋊⟨t⟩. The condition applies and recovers B=1 for every odd p and admissible q. For this chosen layer, J0=1 and W∩V+=1, so the cocycle criterion gives the same conclusion. This uses the C0003 Theorem 1.1(3) folder data and does not certify that every odd simple folder has such a layer.

## Chief-module rank obstruction and regular orbits

Continue the elementary abelian setting of the cocycle lemma and set m=dim E=b−w+d. Let q≠p be a prime and let L≤J0 be elementary abelian of order q^s, and r=ord_q(p). Then
 |B|≥p^d q^{max(0,s−floor(m/r))}.
Indeed, semisimplicity of L on E gives a direct sum of irreducible F_p L-modules. Each nontrivial irreducible has dimension r, and its kernel is a hyperplane in L, so the rank of C_L(E) is at least s−floor(m/r). The cocycle restricts to a homomorphism C_L(E)→E^+ and vanishes on this q-group. Thus C_L(E)≤ker c and its lifts give the displayed lower bound. If B=1 then necessarily d=0 and s≤floor((b−w)/r). This may be stronger than the cardinality bound |J0|≤p^{b−w}; it is conditional on an actual folder and does not produce one.

More generally, if B=1 and L≤J0 has order prime to p, then L has a regular orbit on E under its linear action. Indeed H¹(L,E)=0 by averaging: c|L is a coboundary, c(l)=l·x−x for some x∈E, and injectivity of c forces C_L(x)=1. Conversely, existence of a regular orbit alone does not construct an admissible folder or ensure B=1. No computation or formal verification is claimed.

GPT-6.1 Terra reviewer [model reviewer identity omitted] independently accepted the displacement-cocycle, paired-quotient and regular-orbit sections at exact source `0aef10b81068306fe6beb6f8a925fd9ecbfa9fc3`, conditional on the pinned odd-folder and full-inverted-set inputs. The review checked the quotient action and nonsplit cocycle, exact sequence and coset bounds, product-set identity, qualitative centralizer kernel, prime-q rank bound, and averaging argument. The paired quotient deduction and Q_{p,q} control were checked under the stated C0003 folder data. No universal triviality of H∩τ(H), exact-factorization exhaustiveness or new simple-loop existence follows; no computation or formal verification was used.

## Derived-envelope constraints on the fixed stabilizer

**Deductions with the scoped independent reviews below.** Continue C0010 / 0323.NONBRUCK_ODD under the pinned inputs below. Let Q be a finite simple nonassociative odd-order left Bol loop, with canonical faithful generating folder (G,H,K), canonical inverting involution τ, C=C_G(τ), B=H∩τ(H)=C_H(τ), and A=G/G′. Then:

1. HG′=G and C≤G′. Consequently A is a nontrivial odd abelian quotient of H, and its order satisfies |A| divides gcd(|H|,|Q|), and B≤H∩G′, so |B| divides |H|/|A|.
2. C is a proper subgroup of G′. Consequently |A| is a proper divisor of |Q|. If |H|=|A|, then B=1.
3. G′ acts faithfully and transitively on Q via the canonical permutation action, and H∩G′ is core-free in G′. The subgroups H and τ(H) are not conjugate in G.
4. G is not metabelian. Thus its derived length is at least three.

Proof. The map Q→G/HG′ taking x (with left translation k_x) to k_x HG′ is a surjective loop homomorphism to the group G/HG′: multiplication of representatives differs by an element of H. A nontrivial homomorphism from simple nonassociative Q to a group cannot have trivial kernel, since then Q would be isomorphic to a subgroup of a group. Hence HG′=G. Since τ inverts every element of K and K generates G, τ induces inversion on A. G has odd order, so every τ-fixed element maps to the identity in A, proving C≤G′. Reviewed full-inverted-set counting gives |H|=|C|. Since H surjects onto A, |A| divides |H|; since C≤G′, |H| divides |G′| and |Q|=|G|/|H|=|A|[G′:C], so |A| divides |Q|. Also B≤C≤G′ and B≤H. Nontriviality of A follows because G is nontrivial odd and solvable by Feit–Thompson.

If C=G′, then τ fixes G′ pointwise. The reviewed fixed-normal lemma in this manuscript makes G′ central in G. Since HG′=G, H is normal in G; core-freeness then makes H=1 and the folder associative, contradiction. Thus C<G′ and |Q|/|A|=[G′:C]>1. If |H|=|A|, H∩G′=1 and B≤H∩G′, giving B=1.

For transitivity, HG′=G. The kernel of G′ on G/H is core_{G′}(H∩G′). This subgroup is normal in G′ and normalized by H, because H normalizes H∩G′ and G′ is normal in G. Since G=HG′, the kernel is normal in G and lies in H; it is therefore trivial by core_G(H)=1. The nonconjugacy and metabelian exclusion are proved below.

The term “A divides Q” above is numerical: Q is not asserted to have a quotient isomorphic to A. Indeed simplicity and nonassociativity preclude any nontrivial group quotient. In Q_{p,q}, A≅C_p, |H|=p^p q, |Q|=p^{p+1}q and [G′:C]=p^p q, agreeing with the bounds. The normal closure of B may still be a nontrivial proper τ-stable subgroup of G; strict defect alone has not eliminated it.

Inputs: C0001 faithful-folder and quotient projection; C0007 inversion on K; FKP arXiv:math/0208231v2 Proposition 6.1 and Theorem 4.14 for odd canonical G, source review ab4059e6a9b8d5876e2bffa993bb98e7dac69025; full inverted set and fixed-normal-central theorem in this manuscript reviewed 95f226ac6c02b0153f3c226d823518e0891c1f1d; Feit–Thompson odd-order solvability; C0003 Theorem 1.1(3) for the control. The independent reviews below are conditional on these inputs; no new computation is claimed.

### Stabilizer nonconjugacy and exclusion of metabelian envelopes

Write G⁺=G⋊⟨τ̂⟩, where the formal involution τ̂ induces τ, and Λ=τ̂^G=τ̂K. The reviewed odd-folder geometry gives H∩Λ²={1}. If H and τ(H) were G-conjugate, an element of τ̂G would normalize H. Its order is twice an odd number because G has odd order; an odd power therefore gives an involution λ in τ̂G that still normalizes H. Conjugacy of complements to the odd normal Hall subgroup G gives λ∈Λ. For h∈H, the element h⁻¹h^λ=λ^hλ belongs both to H and to Λ², so it is 1. Thus λ centralizes H. Conjugation by λ induces inversion on G/G′, since inner automorphisms act trivially there and τ induces inversion. Since H surjects onto G/G′, that odd abelian group would have exponent dividing two and hence be trivial. This contradicts nontrivial solvability of G. Therefore H and τ(H) are not G-conjugate. The complement-conjugacy input is Schur–Zassenhaus in Craven, *Finite Group Theory*, Hilary Term 2012, §2.1, Theorem 2.1, p.22, as recorded in REFERENCES.md; here the normal Hall subgroup G is soluble.

Suppose now that G is metabelian and put D=G′. By (3), D is a faithful transitive abelian permutation group and hence regular. Therefore D∩H=1, G=D⋊H, H≅G/D is abelian, and D=[D,H]. We prove directly that H¹(H,D)=0, without assuming coprime orders of H and D.

Fix a prime p dividing |D| and let D_p be the p-primary component. Write H=P×U with P its Sylow p-subgroup and U its p′-Hall subgroup. Averaging over U splits

    D_p = D_p^U ⊕ [D_p,U].

Both terms are P-invariant. Since D_p=[D_p,H], the first term M=D_p^U would satisfy M=[M,P]. But if M≠0, the nonzero F_pP-module M/pM has a nonzero quotient with trivial P-action: its dual has a nonzero fixed vector, as follows by counting P-orbits in the dual vector space. Thus M/[M,P]≠0, a contradiction. Hence D_p^U=0.

For completeness, every additive 1-cocycle δ:H→D_p is a coboundary. Since |U| is invertible on D_p, averaging its restriction to U gives b=|U|⁻¹∑_{u∈U}δ(u) with δ(u)=b−u·b. Subtract this coboundary to arrange δ|_U=0. The commuting elements u∈U and x∈P then give

    u·δ(x) = δ(ux) = δ(xu) = δ(x),

so δ(x)∈D_p^U=0. Therefore the adjusted cocycle vanishes on all of H. Summing over primary components proves H¹(H,D)=0. Because D is characteristic, τ(H) is another complement to D in D⋊H. Every such complement is the graph of a 1-cocycle H→D; a coboundary is removed by D-conjugation. Thus τ(H) is G-conjugate to H, contradicting the preceding nonconjugacy theorem. This proves (4).

This rules out all odd-order simple nonassociative Bol loops with canonical left multiplication group of derived length at most two. It neither bounds the remaining derived length nor proves exact-factorization exhaustiveness. The cohomology vanishing used here is established by the explicit averaging argument, not by a computation or an unverified appeal to a spectral sequence.

### Normal closure of the fixed stabilizer

Suppose B≠1 and set N=⟨B^G⟩. Because τ fixes B pointwise, N is τ-stable. Since B≤C≤G′, we have 1≠N≤G′<G, so the reviewed strict defect gives |H∩N|<|C_N(τ)|. It does not follow that τ fixes N pointwise: conjugation moves B through τ-conjugate positions.

There is a concrete nontrivial τ-inverted element in N. For b∈B and k∈K, τ interchanges b^k and b^{k^−1}, so x=b^k(b^{k^−1})^−1 lies in N and is τ-inverted, hence x∈K. If all such x were 1 for one nontrivial b, then b would centralize k² for every k∈K, and, since G has odd order, would centralize K and G. But B∩Z(G)=1 because B≤H and core_G(H)=1. Therefore K∩N is nontrivial. This by itself does not force the projected section modulo N to be a transversal; strict defect in fact prevents it.

If N is nilpotent, HN<G. Otherwise P=H∩N is a proper subgroup of N, normalized by H. Because HN=G and B≤P, the normal closure of B under G lies in the normal closure of P under N. That latter normal closure is proper: in a finite nilpotent group every maximal subgroup is normal, so a proper P lies in a proper normal subgroup. This contradicts N=⟨B^G⟩. In particular, if B≤F(G), its normal closure is nilpotent and cannot be transitive. More generally the same conclusion applies to the normal closure of any nontrivial subset of B contained in F(G).

This is a genuine normal-closure restriction, not an exclusion of B≠1. It leaves a proper intransitive nilpotent normal closure compatible with the strict-defect inequalities, and it does not imply equality |H∩N|=|C_N(τ)|. The known non-Bruck product control is nonsimple and has such an equality, but it does not decide the simple-loop case.

### Independent review of the derived-envelope deductions

GPT-6.1 Terra reviewers [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the entire derived-envelope section and its subsections at exact source `e896039d004ff3882621aca115b1a39cc8fed207`, conditional on the stated canonical-folder, odd-order, full-inverted-set, fixed-normal, strict-defect and C0003 inputs. They checked the abelianization homomorphism and divisor bounds, faithful derived-subgroup action, marked-class nonconjugacy argument, metabelian exclusion including the shared-prime averaging step, and nilpotent normal-closure restriction. They checked the numerical Q_{p,q} control against its cited construction, without reviewing all of C0003. A third independent reviewer, [model reviewer identity omitted], accepted specifically the stabilizer nonconjugacy and metabelian-exclusion subsection at that exact source; this narrower review excludes the following normal-closure subsection. No computation or formal verification was performed. The reviews do not establish B=1, exact-factorization necessity, a bound on remaining derived length, or an odd-loop classification.

## Faithful stabilizer action on the derived group

**Bounded deduction for 0323:C0010, with the scoped independent reviews below.** If a group G has a normal subgroup D, G=HD and core_G(H)=1, then H∩C_G(D)=1. Indeed this intersection is normalized by H, because H normalizes D, and centralized by D. It is therefore normal in HD=G and contained in H, so core-freeness makes it trivial.

Apply the reviewed identity G=HG′ above to a canonical simple nonassociative odd Bol folder. Then H acts faithfully on D=G′ by conjugation, and H∩Z(D)=1, without any assumption that D is nilpotent or Z(D) central in G. If D is nilpotent with class-two Sylow factors, each S_i=H∩P_i is abelian: its commutator lies in S_i∩Z(P_i), and Z(P_i)≤Z(D). This gives genuine necessary stabilizer constraints for the noncentral-center branch. It does not force Z(D)≤Z(G), a split extension over D, disjointness of H and τ(H), or a G-loop property. The separate noncentral-center construction retains its own review boundary.

The derived-length lower bound is attained by the later [cross-coupled extraspecial family](odd-cross-extraspecial.md), reviewed at `3b47eee4f5bfb43983b5ba474dff3689796eb9ad`: its canonical G has nonabelian class-two derived subgroup and derived length three. That construction also refutes the attempted universal paired-minimal step toward exact-factorization necessity. It does not give an upper bound on derived length for arbitrary simple odd Bol loops.

At exact source `379317e583fa1e0c9171d526562c4f7e484d7d19`, GPT-6.1 Terra reviewers [model reviewer identity omitted], [model reviewer identity omitted] and [model reviewer identity omitted] separately accepted this faithful-stabilizer-action subsection and its class-two consequence, conditional on the previously reviewed G=HG′ identity. No computation or further classification conclusion is asserted.
