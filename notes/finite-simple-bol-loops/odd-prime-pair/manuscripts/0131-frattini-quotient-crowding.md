# Frattini quotient crowding and the single-axial-packet obstruction

**Mira Cult**

We use the canonical odd reciprocal two-axis reduction for a finite simple proper Bol loop of order $`p^a q`$, with odd distinct primes and top order $`p^k`$, $`k\ge2`$. Write $`D,H,t`$ for the actual faithful left group, stabilizer and sign, $`N=O_p(D)`$, $`T`$ for the inverted marks, and $`\Lambda=Tt`$ for the unique outside involution class. The actual sharp-folder condition is that every stabilizer coset, for every conjugate of $`H`$, meets $`T`$ once. Equivalently $`\Lambda^2`$ avoids $`H`$ off identity and the mark count agrees with its index.

## 1. The exact loss upon taking a quotient

Let $`F\le N`$ be signed-normal in $`D`$, and use bars for reduction modulo $`F`$. Each right coset of $`\bar H`$ contains exactly
```math
\Delta_F=\frac{|C_F(t)|}{|F\cap H|}
```
distinct inverted quotient marks. Indeed its inverse image is a right coset of $`FH`$, consisting of $`[F:F\cap H]`$ right cosets of $`H`$, one mark in each. The images of the outside involutions exhaust the outside involutions in the quotient: the latter are all conjugate to the image of $`t`$ by odd-order Sylow conjugacy. Each quotient mark has equally many preimages in $`T`$ by conjugation equivariance on $`\Lambda`$ and its image. Their common number is $`[F:C_F(t)]`$ by the class size ratio and coprime fixed-point lifting through $`F`$. Dividing gives the formula. This argument also applies to all conjugate stabilizers, since their intersections with $`F`$ have the same order. Thus the ordinary sharp stabilizer coset condition descends exactly if $`\Delta_F=1`$, which the strict signed-normal cut excludes for every nontrivial proper $`F`$ in the simple folder. Such a quotient of the marked data is not a quotient loop obtained by reusing the projected marks and projected stabilizer.

## 2. Projected top collisions for the Frattini quotient

Take $`F=\Phi(N)`$, $`M=N/F`$, $`U=(H\cap N)F/F=\bar H\cap M`$, and write $`c=\log_p\Delta_F`$, $`e=\dim(U\cap M^-)`$. We may replace $`H`$ by a conjugate: avoidance is preserved by conjugacy invariance of $`\Lambda^2`$, and neither multiplicities nor normal-cut sizes change. Normalize the actual upper image of $`H`$ to $`B_2\rtimes C_{p^k}`$ in $`D/N`$, removing a first-axis displacement by diagonal $`q`$ conjugacy as in the [elementary positive projection proof](../reviews/first-degree-prime-pair-upstream-necessity-audit.md). In the sign-stable $`q`$-normalizer take an inverted lift $`h`$ of a top generator by sign displacement; its order need not equal the top order. The normalized $`\bar H`$ contains a genuine lift $`a_0\bar h`$ with $`a_0\in M`$. Its conjugation on $`M`$ equals the action $`R`$ of $`h`$, since $`M`$ is abelian. Thus $`U`$ is $`R`$-stable; $`R^{p^k}=1`$ holds on $`M`$ because $`h^{p^k}\in N`$ acts trivially on the Frattini quotient.

Write $`\pi_+=(1+t)/2`$ on $`M`$. The positive codimension is exactly
```math
\delta=\dim(M^+/\pi_+ U)=k-c+e\le k .
```
In fact $`[D:H]=q p^k[N:C_N(t)]`$ from the signed mark count and the fixed diagonal in the upper quotient; also $`[D:H]=q[N:H\cap N]`$ from the physical projected stabilizer index. Divide this core count by $`[F:F\cap H]`$, and lift fixed points through $`F`$, to obtain $`[M:U]=p^{\dim M^-+k-c}`$. The projection kernel contributes $`e`$ to the codimension. Finally $`U\cap M^-\subseteq \bar H\cap\bar T`$, so $`p^e\le\Delta_F`$ by Section 1. In particular $`\delta`$ need not be measured using an injective positive projection in the quotient.

For every $`1\le j<p^k`$ with $`p^{\nu_p(j)}-1\ge2\delta`$, the projected subgroup $`\bar H`$ contains a nonidentity product of two quotient outside involutions with actual top image the $`j`$th power of the generator. To see this put $`Z=R-R^{-1}`$, which anticommutes with sign. The nilpotent $`Z^2`$ preserves $`\pi_+ U`$, hence its $`\delta`$th power kills the positive quotient. The first component of $`(a_0\bar h)^j`$ is $`\Sigma_j(R)a_0`$. In characteristic $`p`$, the polynomial $`\Sigma_j(X)`$ is divisible by $`(X-1)^{p^{\nu_p(j)}-1}`$; $`R-1`$ and $`Z`$ differ by a commuting unit. The indicated exponent is even, so positive projection of the first component therefore belongs to $`\pi_+ U`$. Cancel a matching element of $`U`$, leaving $`v\bar h^j`$ with $`t(v)=-v`$. This is $`(vt)(t\bar h^j)`$, a product of two outside involutions, and is nonidentity by its top image. In particular $`j=p^{k-1}`$ works outside $`(p,k)=(3,2)`$. This is a projected collision only. If one lifts its two factors to the original outside class and compares their product with an actual member of $`H`$ over the collision, the remaining difference belongs to $`F`$; the genuine folder requires that difference to avoid the actual stabilizer fiber. We do not assert a contradiction without controlling this phase.

## 3. An actual exclusion for nonabelian cores with one axial packet

Assume $`N`$ is nonabelian, sign fixes $`F=\Phi(N)`$ pointwise, and $`M=N/F`$ consists of exactly one nontrivial simultaneous top/Frobenius packet on each of the two axial supports, multiplicity one, exchanged by sign, with no other packet. (An axial weight is nontrivial on its own $`q`$ axis and trivial on the other.) This branch is impossible.

First $`F`$ is central in $`D`$: on $`F`$ conjugation by an inverted mark agrees with conjugation by its inverse because $`t`$ restricts to the identity on $`F`$. The marks have odd order, so each acts trivially on $`F`$; they generate $`D`$. Hence $`H\cap F=1`$ by core-freeness. In particular $`N`$ has nilpotency class two and $`[H\cap N,H\cap N]=1`$. The commutator induces an alternating bilinear form on $`M`$ with values in the elementary abelian subgroup $`\Omega_1(F)`$: commutators are central, and all their orders divide $`p`$ since the $`p`$th powers of $`N`$ belong to $`F`$. Contraction by any prime-field linear functional is invariant under the ambient conjugation action, since $`F`$ is central. The actual subspace $`U`$ is isotropic for every contraction.

Let $`A_1,A_2`$ denote the two axial subspaces. Each has dimension $`d=\mathrm{lcm}(p^k,\mathrm{ord}_q(p))`$ and is irreducible for the group generated by its own axis and the top: over a splitting field, any invariant subspace is a sum of the one-dimensional distinct weight spaces, the subset being invariant under both top and Frobenius; those permutations are transitive on the packet. The cross bracket $`[A_1,A_2]`$ is zero because invariance under the first $`q`$ axis, which fixes $`A_2`$, annihilates all cross pairings with the fixed-point-free $`A_1`$. Nonabelianness and sign exchange imply that the self bracket on each axis is nonzero. Choose a contraction nonzero on $`A_1`$; its radical is invariant, hence zero by irreducibility. A nonzero contraction on $`A_2`$ likewise has zero radical.

Normalize $`H`$ as before so it contains $`B_2`$ and has a lift with pure top projection. The $`B_2`$-moving part of $`U`$ is contained in $`A_2`$ by averaging, and is stable under the top. It is therefore zero or all of $`A_2`$, and the latter contradicts isotropy. Thus $`U\subseteq A_1`$ and $`\dim U\le d/2`$. On the other hand fixed sign on $`F`$ yields $`\dim M^-=d`$, and Section 2 gives
```math
\dim U=d+\log_p|F|-k .
```
Because $`d\ge p^k>2k`$, this is strictly larger than $`d/2`$, contradiction. No exponent-$`p`$ assumption on $`N`$ is needed. This exclusion does not treat noncentral or sign-moving Frattini groups, or cores having extra axial, fixed or mixed packets.
