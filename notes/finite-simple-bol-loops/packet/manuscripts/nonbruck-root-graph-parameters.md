# Root-graph parameters for an even affine family

This manuscript-local parameterization concerns C0010 [context outside this selected packet: `../claims/C0010.md`] and the exact-factorization family in C0004 [context outside this selected packet: `../claims/C0004.md`]; it allocates no claim ID. Its construction, isomorphism and counting arguments have the scoped independent reviews below, conditional on the cited folder inputs. The appended exhaustion argument has separate scoped reviews at the source recorded below. Together they classify all nontranslation regular subgroups in this natural SL₂(q) affine family and the loops they construct, not all even non-Bruck loops or all loops of the orders below. Literature novelty of the parameterization is unverified.

## Data and construction theorem

For each prime $p$ and integer $f\ge1$ with $q=p^f\ge4$, let $V=\mathbb F_q^2$ as an additive group, $A=\operatorname{SL}_2(q)$ in its natural action, $X=V\rtimes A$, and

$$u(t)=\begin{pmatrix}1&t\\0&1\end{pmatrix},\qquad U=\{u(t):t\in\mathbb F_q\},\qquad W=\mathbb F_q(1,0).$$

For each nonzero $\mathbb F_p$-linear map $\phi:\mathbb F_q\to\mathbb F_q$, put

$$\gamma_\phi(x,y)=u(\phi(y)),\qquad B_\phi=\{(v,\gamma_\phi(v)):v\in V\}\le X.$$

Let $Q_\phi$ be the left Bol loop of the exact factorization $X=B_\phi A$ using the construction in [C0002, Proposition 1.1](../proofs/C0002.md). The following holds, conditional on the precise C0001/C0002/C0004 folder and isomorphism results:

1. Every $Q_\phi$ is finite simple proper left Bol, has order $q^3(q^2-1)$, and belongs to the $\tau(H)\ne H$ even branch of PROBLEM [context outside this selected packet: `../PROBLEM.md`].
2. For fixed $q$, $Q_\phi\cong Q_\psi$ if and only if there exist $c,d\in\mathbb F_q^\times$ and $j\in\{0,\ldots,f-1\}$ such that

   $$\psi(x)=c\,\bigl[\phi(d\,x^{p^{-j}})\bigr]^{p^j}\qquad(x\in\mathbb F_q),\tag{1}$$

   where $p^{-j}$ denotes the inverse Frobenius automorphism on $\mathbb F_q$. Different $q$ give different loop orders. Thus the indicated finite orbit space is explicit isomorphism data for this subfamily; no efficiency or whole-order census is claimed.

The source construction is Nagy, *Representations of loops in groups and projective planes*, DSc dissertation, title page 2014, [primary PDF](https://real-d.mtak.hu/722/7/NagyGaborPeter_doktori_mu.pdf), Proposition 3.12 and Corollary 3.13, printed pp. 34–35. It uses right Bol conventions; taking opposites transports the construction. The source's hypotheses are checked below. C0004, Theorem 1.1 and Theorem 2.1(1)–(3), have two scoped independent reviews at source revision `87a0895eec2cf7b690dafab5ca3292fb05147a03`; its exact isomorphism theorem remains an explicit conditional input here. Those reviews do not review this new parameterization.

## Construction and branch

The map $\gamma_\phi$ is a homomorphism of additive groups, has image the nontrivial root subgroup $T_\phi=\{u(\phi(y)):y\in\mathbb F_q\}\le U$, and has kernel containing $W$; moreover $[T_\phi,V]\le W$. Nagy writes his graph using $\gamma(-v)$; replacing his parameter by $-\phi$ gives the displayed convention. His Proposition 3.12 gives a subgroup $B_\phi$ and an exact factorization. Explicitly, in any characteristic,

$$(v,u(\phi(y)))(w,u(\phi(y')))
 =(v+u(\phi(y))w,\;u(\phi(y)+\phi(y'))),$$

whose second vector coordinate is $y+y'$; hence the displayed set is closed. Its projection onto $V$ is bijective, so it acts regularly on $V$, has order $q^2$, and intersects $A$ trivially. It is not the translation subgroup because its projection to $A$ is $T_\phi\ne1$.

For $q\ge4$, $A=\operatorname{SL}_2(q)$ is perfect and $A/Z(A)\cong\operatorname{PSL}_2(q)$ is nonabelian simple; its natural module is faithful and irreducible over $\mathbb F_p$ (SL₂(q) is transitive on its nonzero vectors). Thus the finite quasisimple affine hypotheses of C0004, Theorem 2.1, apply. Alternatively, Nagy's Proposition 3.12(iii) applies because $A=A'$ is irreducible and the normal closure of nontrivial $T_\phi$ is $A$: its image in $A/Z(A)$ is nontrivial and normal, and perfectness excludes a proper subgroup surjecting onto $A/Z(A)$. These are established-source/conditional deductions, not a new proof of C0004. Since $|V|=q^2$ and $|A|=q(q^2-1)$, the order is $q^3(q^2-1)$, strictly increasing in $q$.

Here $X'=X$, so the generated faithful folder is $(X\times X,B_\phi\times A,\{(x,x^{-1}):x\in X\})$ under C0002. Coordinate swap inverts the section and equals the canonical $\tau$ by C0007 uniqueness. Since $|B_\phi|=q^2\ne |A|$, the swapped stabilizer $A\times B_\phi$ differs from $B_\phi\times A$. Thus $\tau(H)\ne H$. Its order is even: $q$ is even when $p=2$, while $q^2-1$ is even when $p$ is odd. This is the stated branch condition; no inference about isotopy to a Bruck loop is made.

## Isomorphism reduction and normalizer

By C0004, Theorem 2.1(3), for fixed $q$ an isomorphism $Q_\phi\cong Q_\psi$ is equivalent to an automorphism $\alpha$ of $X$ with $\alpha(A)=A$ and $\alpha(B_\phi)=B_\psi$. Its proof recovers the two direct factors of the faithful folder and rules out their interchange using $|B_\phi|=q^2$ versus the nonsolvable order $|A|$. Thus this step accounts for possible folder-factor swaps through the cited theorem; it is not an assumption that every presentation has a fixed ordering.

The group $V$ is the unique minimal normal subgroup of $X$: it is irreducible, $C_X(V)=V$, and any nontrivial normal subgroup intersects $V$ nontrivially. Hence $\alpha(V)=V$. Since $\alpha(A)=A$, its restriction $g=\alpha|_V\in\operatorname{GL}_{2f}(p)$ determines its action on $A$ by $a\mapsto gag^{-1}$. Conversely every $g\in N_{\operatorname{GL}_{2f}(p)}(A)$ defines such an automorphism of $X$. This addresses potential quotient automorphisms and complement-section changes: after the cited isomorphism theorem requires preservation of the chosen complement $A$, the faithful action forces the quotient automorphism, and no independent translation cocycle remains.

We compute this normalizer. The endomorphism algebra $\operatorname{End}_{\mathbb F_p A}(V)$ is exactly $\mathbb F_q$ acting by scalar multiplication. To see this, write an $\mathbb F_p$-linear endomorphism as a $2\times2$ block matrix of endomorphisms of $\mathbb F_q$. Commutation with all upper and lower unipotents $u(t)$ and $\ell(t)=\left(\begin{smallmatrix}1&0\\t&1\end{smallmatrix}\right)$ forces off-diagonal blocks to vanish and the two diagonal blocks to agree and commute with every multiplication-by-$t$ map. Such a block is multiplication by its value at $1$, proving the assertion. A normalizer element conjugates this scalar algebra to itself and so induces an automorphism $x\mapsto x^{p^j}$ of $\mathbb F_q$. After composing with inverse coordinatewise Frobenius, it is $\mathbb F_q$-linear. Conversely $\operatorname{GL}_2(q)$ and coordinatewise Frobenius normalize $\operatorname{SL}_2(q)$. Therefore

$$N_{\operatorname{GL}_{2f}(p)}(A)=\Gamma\operatorname{L}_2(q).$$

The projection of $B_\phi$ to $A$ is $T_\phi\ne1$, and an admissible $g$ carries $T_\phi$ onto $T_\psi$. Every nonidentity element of $U$ has fixed space exactly $W$, so $C_V(T_\phi)=C_V(T_\psi)=W$; consequently $g$ preserves $W$ and is upper triangular semilinear. Conversely, the parameter formula below explicitly identifies when such a map carries $B_\phi$ to $B_\psi$, including its projected root subgroup. Write such a map as $g=D\sigma_j$ with

$$D=\begin{pmatrix}a&b\\0&e\end{pmatrix},\quad a,e\ne0,\qquad \sigma_j(x)=x^{p^j}.$$

Conjugation sends $u(t)$ to $u((a/e)t^{p^j})$, while the second coordinate of $g^{-1}(x,y)$ is $(e^{-1}y)^{p^{-j}}$. Thus the parameter of $g B_\phi g^{-1}$ is

$$\psi(y)=\frac ae\left[\phi\!\left(e^{-p^{-j}}y^{p^{-j}}\right)\right]^{p^j}.$$

The upper-right entry $b$ has no effect on the parameter. Taking $c=a/e$ and $d=e^{-p^{-j}}$ yields (1); conversely arbitrary nonzero $c,d$ arise by choosing $e=d^{-p^j}$ and $a=ce$. Every such $g$ gives an automorphism of $X$ preserving $A$ and carrying $B_\phi$ to the corresponding $B_\psi$. This proves the criterion conditional on C0004's isomorphism interface.

## Closed orbit count

Every $\mathbb F_p$-linear endomorphism of $\mathbb F_q$ has a unique linearized polynomial representation

$$\phi(x)=\sum_{i=0}^{f-1}a_i x^{p^i},\qquad a_i\in\mathbb F_q.$$

Indeed, the $q^f=p^{f^2}$ coefficient vectors give distinct functions: their difference is a polynomial of degree at most $p^{f-1}<q$, so it cannot vanish at every field element unless it is zero. There are exactly $p^{f^2}$ linear endomorphisms. Under (1), the coefficients transform as

$$a_i' = c\,a_i^{p^j}e^{p^i},\qquad c,e\in\mathbb F_q^\times,\quad 0\le j<f,$$

where $e=d^{p^j}$ can be arbitrary. Hence the nonempty support $I=\{i:a_i\ne0\}$ is invariant. In particular the maps $\phi_I(x)=\sum_{i\in I}x^{p^i}$, for nonempty $I\subseteq\{0,\ldots,f-1\}$, represent at least $2^f-1$ distinct classes, conditional on the isomorphism interface. This sharpens the $f$ singleton representatives below.

For a fixed support $I$ of size $s\ge2$, choose $i_0\in I$ and divide every coefficient by $a_{i_0}$, using the scalar $c$. Identify $\mathbb F_q^\times$ with the cyclic group $C_n=\mathbb Z/n\mathbb Z$, $n=p^f-1$, using a fixed primitive element. The logarithms of the remaining coefficient ratios form $(C_n)^{s-1}$. The scalar $e$ acts by translation by multiples of

$$w=(p^i-p^{i_0})_{i\in I\setminus\{i_0\}},$$

and Frobenius acts by multiplication by $p$. Thus the parameter orbits for this support are the orbits of multiplication by $p$ on

$$D_I=(C_n)^{s-1}/\langle w\rangle.$$

Put $h=\gcd(f,\{i-i_0:i\in I\})$ and $g=p^h-1$. Since powers of $p$ are units modulo $n$ and $\gcd(p^f-1,p^m-1)=p^{\gcd(f,m)}-1$, we have $\gcd(n,\{w_i\})=g$. Integer Smith reduction sends $w$ to $(d,0,\ldots,0)$, where $d$ is the gcd of its integer coordinates; the induced unimodular map on $(C_n)^{s-1}$ gives

$$D_I\cong (C_n)^{s-2}\times C_{\gcd(n,d)}=(C_n)^{s-2}\times C_g.$$

This group isomorphism commutes with multiplication by any integer. Burnside's lemma for the (possibly nonfaithful) $C_f$-action generated by multiplication by $p$ therefore gives the exact **conditional** support count

$$N_I=\frac1f\sum_{j=0}^{f-1}
 (p^{\gcd(f,j)}-1)^{s-2}(p^{\gcd(h,j)}-1).\tag{2}$$

The fixed-point count uses $\gcd(p^a-1,p^j-1)=p^{\gcd(a,j)}-1$, including $j=0$ with $\gcd(a,0)=a$. Singleton supports have one orbit, since output scalars normalize their unique nonzero coefficient. Therefore the total for this subfamily is

$$f+\sum_{\substack{I\subseteq\{0,\ldots,f-1\}\\ |I|\ge2}}N_I.\tag{3}$$

For $p=2$, the [finite certificate](../code/verify_nonbruck_root_graph.py) evaluates (3) for $f=2,3,4$, obtaining $3,9,91$, and separately enumerates all nonzero maps at those parameters, obtaining the same orbit counts. For any prime $p$, the formula gives $N_{p,1}=1$ and $N_{p,2}=p+1$; the script checks these arithmetic identities at selected odd primes. This checks finite arithmetic and three parameter actions only. The coefficient argument, general Smith/Burnside calculation and resulting uniform claim have the scoped independent reviews below; no count of all loops at these orders follows.

## Divisor-only form

For $h\mid f$, let $M_h$ be the number of nonzero elements of $\mathbb F_{p^h}$ of exact degree $h$ over $\mathbb F_p$:

$$M_h=p^h-1-\sum_{\substack{d\mid h\\d<h}}M_d.$$

Writing $\varphi_{\rm E}$ for Euler's totient function, the same conditional count (3) can be computed without enumerating supports as

$$N_{p,f}=\frac1f\sum_{s\mid f}\frac{\varphi_{\rm E}(f/s)}{(p^s-1)^2}
 \sum_{h\mid s} hM_h\bigl(p^{fs/h}-1\bigr).\tag{4}$$

For a derivation, apply Burnside directly to the transformations $(c,e,j)$ on coefficient vectors, including the nonfaithful parameterization: the group has order $f(q-1)^2$, and its kernel causes no difficulty in Burnside's formula. Fix $j$, put $s=\gcd(f,j)$ and write $\mathbb F_{p^s}$ for the fixed field. A nonzero coefficient satisfying $a=c e^{p^i}a^{p^j}$ exists exactly when $\operatorname{Norm}_{q/p^s}(c)\operatorname{Norm}_{q/p^s}(e)^{p^i}=1$; in that case there are $p^s-1$ nonzero choices. This follows from the cyclicity of $\mathbb F_q^\times$: the kernel of $a\mapsto a^{p^j-1}$ has size $p^s-1$ and its image is the norm-one subgroup.

Put $C=\operatorname{Norm}(c)$ and $E=\operatorname{Norm}(e)$. If $E$ has exact degree $h\mid s$, exactly $h$ values of $C$ make at least one coefficient index eligible; for each, precisely $f/h$ of the indices $0,\ldots,f-1$ are eligible. Each eligible coefficient has $p^s$ choices including zero, so the number of nonzero fixed vectors is $p^{sf/h}-1$. There are $M_h$ such elements $E$. Each pair $(C,E)$ has $((q-1)/(p^s-1))^2$ preimages $(c,e)$, which cancels the $(q-1)^2$ factor in the Burnside denominator. Finally, exactly $\varphi_{\rm E}(f/s)$ choices of $j\in\{0,\ldots,f-1\}$ have $\gcd(f,j)=s$, including $j=0$ when $s=f$. This proves (4) as an orbit-count identity, conditional on the preceding identification of parameter orbits with loop isomorphism classes.

The exact-rational implementation in [the certificate](../code/verify_nonbruck_root_graph.py) compares (3) and (4) for $p=2$, $2\le f\le8$, and for odd-characteristic arithmetic controls. Both formulas and the algebraic isomorphism interface have the scoped independent reviews below; agreement at finitely many parameters is not a proof of the general identities.

## Finite control and limits

The [finite parameter-orbit certificate](../code/verify_nonbruck_root_graph.py) enumerates every nonzero $\mathbb F_2$-linear map and the transformations in (1) for $q=4,8,16$; it does not enumerate odd-characteristic fields. From the repository root run

```sh
python3 problems/0323-finite-simple-non-moufang-bol-loops/code/verify_nonbruck_root_graph.py
```

The revised producer run used Python 3.9.6. It enumerated all $15$ nonzero maps for $q=4$, obtaining orbit sizes $9$ at rank one and $3,3$ at rank two. For $q=8$ it enumerated all $511$ nonzero maps: rank one has size $49$; rank two has sizes $49,49,49,147$; and rank three has sizes $7,7,7,147$. For $q=16$ the producer run enumerated all $65535$ nonzero maps and found $91$ orbits. Root independently read and ran the final generalized certificate with Python 3.12.14, obtaining the same enumerations and the agreement of both formulas for the stated binary and odd-characteristic arithmetic controls. The calculation checks parameter orbits only; it does not verify loop axioms, simplicity, the normalizer, or the isomorphism interface. The extended certificate and deduction have the scoped independent reviews below and are not a census of all loops at any of those orders.

## Uniform lower bounds for this subfamily

Conditional on the construction and isomorphism inputs, the upper triangular semilinear normalizer induces at most $f(q-1)^2$ transformations on the parameter space. Every orbit therefore has at most that many elements. There are $p^{f^2}-1$ nonzero $\mathbb F_p$-linear maps, so the number of isomorphism classes in this subfamily is at least

$$\left\lceil\frac{p^{f^2}-1}{f(p^f-1)^2}\right\rceil.$$

In particular, for $p^f\ge4$ this is strictly greater than $p^{f^2-2f}/f$, since $p^{f^2}-1>p^{f^2}(1-p^{-f})^2$. This bound concerns only the explicitly constructed subfamily. The invertible maps give the smaller independently meaningful bound $\lceil|\operatorname{GL}_f(p)|/[f(p^f-1)^2]\rceil$, where $|\operatorname{GL}_f(p)|=\prod_{i=0}^{f-1}(p^f-p^i)$.

There are also at least $f$ explicit classes, represented by $\phi_k(x)=x^{p^k}$ for $0\le k<f$. Transformation (1) sends each $\phi_k$ to a nonzero scalar multiple of itself, so it cannot change $k$. Distinct exponents give distinct functions: evaluating at $1$ removes any scalar ambiguity, and distinct Frobenius automorphisms of $\mathbb F_{p^f}$ are different. These lower bounds inherit C0004's stated scoped review limits and have the independent reviews below.

Nagy's dissertation §5.4, Problems 5.14–5.15, printed p. 57, asks historically for a simple Bol loop neither a $G$-loop nor an isotope of a Bruck loop, and for a finite simple proper Bol loop with primitive one-sided multiplication group. The present exact-factorization loops are $G$-loops and have imprimitive one-sided multiplication group under the cited construction results, so this subfamily does not settle either question. This source comparison is not a current literature or novelty audit.

## Independent review of construction and counts

GPT-6.1 Terra reviewers [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the construction, full isomorphism criterion, support and divisor formulas, and lower bounds at exact source `8ad35e2dbed5179f70be146d73b61ae80bde5555`, conditional on C0001/C0002/C0004 and canonical inversion inputs. The needed C0004 Theorem 1.1 and Theorem 2.1(1)–(3) have separate scoped acceptances at `87a0895eec2cf7b690dafab5ca3292fb05147a03`. Both checked arbitrary characteristic, noninvertible nonzero maps, the possible SL₂ center, the full semilinear normalizer, and both independent Burnside derivations. Both read and independently ran the pinned certificate with Python 3.12.14, reproducing binary field orbit counts 3,9,91 and the stated formula comparisons. The computations check parameter data, not loop identities or an all-loop census. These reviews do not audit source novelty, the dissertation comparison or the C0004 aggregate. **They do not cover the following exhaustion extension, which was added after this source revision.**

## Exhaustion of the natural-module affine family

Let $q=p^f\ge4$, $V=\mathbb F_q^2$, $A=\operatorname{SL}_2(q)$, and $X=V\rtimes A$. Every subgroup $Y\le X$ acting regularly on $V$ is conjugate by an element of $A$ to $B_\phi$ for some $\mathbb F_p$-linear map $\phi:\mathbb F_q\to\mathbb F_q$. The zero map gives the translation group $V$; all other maps give the nontranslation regular subgroups studied above. Consequently, subject to the earlier C0004 construction and isomorphism interface equations (1)–(4) classify **all loops arising from the nontranslation regular subgroups in this natural-module affine exact-factorization family**. They do not classify all simple Bol loops of the same orders or all even non-Bruck envelopes. The graph map is unique after fixing the conjugating element and the resulting choice of $U$; different choices are accounted for by the isomorphism action above.

*Proof.* Regularity gives $|Y|=|V|=q^2$, so $Y$ is a $p$-group, and the projection $\pi(Y)\le A$ is a $p$-subgroup. The root group $U$ has order $q=|A|_p$ and is a Sylow $p$-subgroup. Conjugating $Y$ by an element of $A$ therefore lets us assume $\pi(Y)\le U$. This conjugation preserves the complement $A$ and gives equivalent exact-factorization data. Put $P=V\rtimes U$ and write its elements as $(x,y,t)$ for $((x,y),u(t))$. Its group law is

$$(x,y,t)(x',y',t')=(x+x'+ty',\ y+y',\ t+t').$$

The subgroup $Z=\{(x,0,0):x\in\mathbb F_q\}=W$ is central in $P$, and $P/Z\cong\mathbb F_q^2$ as an additive $\mathbb F_p$-space with coordinates $(y,t)$. Its commutator pairing is

$$[(y,t),(y',t')]=ty'-t'y\in Z\cong\mathbb F_q,$$

up to the harmless choice of commutator convention. Let $C=Y\cap Z$ and $L=YZ/Z$. If $c=\dim_{\mathbb F_p}C$, then $\dim L=2f-c$, since $|Y|=p^{2f}$ and $|Y\cap Z|=p^c$.

Suppose $c<f$. Choose a nonzero $\mathbb F_p$-linear functional $\ell:\mathbb F_q\to\mathbb F_p$ vanishing on $C$. The scalar form

$$b_\ell((y,t),(y',t'))=\ell(ty'-t'y)$$

on $\mathbb F_q^2$ is alternating and nondegenerate: if $t\ne0$, multiplication by $t$ is surjective and a suitable $y'$ gives $\ell(ty')\ne0$; if $t=0$ and $y\ne0$, a suitable $t'$ works. The subspace $L$ is totally isotropic, since $[Y,Y]\le Y\cap Z=C$. A totally isotropic subspace of a nondegenerate alternating space of dimension $2f$ has dimension at most $f$, whereas $\dim L=2f-c>f$, a contradiction. Thus $C=Z$ and $Z\le Y$.

Now $\dim L=f$. Regularity gives $Y\cap A=1$ because $A$ is the stabilizer of $0\in V$. In particular $Y\cap U=1$. If $(0,t)\in L$, some $(x,0,t)\in Y$; as $Z\le Y$, subtracting $(x,0,0)$ shows $(0,0,t)\in Y\cap U$, so $t=0$. Thus projection $L\to\mathbb F_q$ onto the $y$ coordinate is injective and hence bijective by dimension. Consequently $L$ is the graph of a unique $\mathbb F_p$-linear map $t=\phi(y)$. Since $Z\le Y$, the subgroup $Y$ is the full preimage of $L$ in $P$, namely

$$Y=\{(x,y,\phi(y)):x,y\in\mathbb F_q\}=B_\phi.$$

This equality also shows $Y=V$ exactly when $\phi=0$. For nonzero $\phi$, the construction and isomorphism results above apply. This finishes the exhaustion. $\square$

GPT-6.1 Terra reviewers [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted this exhaustion argument at exact source `508e8f23a95c6817e9ec3c1b29ff4d5836caa843`. Both checked the Sylow conjugation inside SL₂(q), the group law and alternating form in every characteristic, the isotropic dimension contradiction, regularity and the full-preimage graph conclusion. The consequent loop classification uses the construction, isomorphism and count interface separately reviewed at `8ad35e2dbed5179f70be146d73b61ae80bde5555`; it does not concern other affine modules or all loops of the displayed orders. These are independent mathematical argument reviews, with no additional computation or formal verification.
