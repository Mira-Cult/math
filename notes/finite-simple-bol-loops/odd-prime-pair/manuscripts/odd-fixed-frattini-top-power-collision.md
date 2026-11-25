# Actual top-power collisions for fixed-Frattini purely axial cores

**Mira Cult**

**Status:** author proof, pending independent proof audit. This is not a statement about mixed weights, a sign-moving Frattini subgroup, or unrestricted Bol classification.

Retain the canonical odd signed two-axis folder: $`D=\mathrm{LMlt}(Q)`$, $`H`$ is its actual core-free stabilizer, $`t`$ the sign in the odd-order extension, and $`\Lambda`$ its outside conjugacy class. Thus $`H\cap\Lambda^2=1`$. The canonical $`p`$-core $`N`$ has quotient $`D/N=B\rtimes C_{p^k}`$, with $`B=B_1B_2\cong C_q^2`$, the sign exchanging the reciprocal axes, and $`\pi(H)\cap B=B_2`$ with $`\pi(H)`$ surjecting onto the top. Assume $`N`$ is nonabelian, $`F=\Phi(N)`$ is pointwise sign-fixed, and $`N/F`$ has only nontrivial axial $`B`$-weights (no mixed or fixed weights). The two axial modules have equal dimension $`d`$; multiplicities, self-duality, and simultaneous nondegeneracy are unrestricted. We use the established signed normalizer reduction and physical normalization from the two-axis setup; see the [fixed-Frattini reduction](0132-fixed-frattini-multiplicity-one.md) and [physical phase analysis](0133-fixed-frattini-repeated-packets.md).

## The obstruction

Write $`b=\log_p|F|`$. Identify the two additive axial modules using the sign, and let $`U_1,U_2\subseteq A`$ be the two physical axial components of $`H\cap N`$ modulo $`F`$. Put $`T=U_1+U_2`$ and $`\Delta=\operatorname{codim}_A T`$. If $`s=p^r`$, $`0\le r\le k-2`$, and $`s-1\ge\Delta`$, then the physical stabilizer contains a nonidentity element of $`\Lambda^2`$, a contradiction. In particular:

- No such core occurs for $`p\ge5,\ k\ge3`$, or for $`p=3,\ k\ge4`$.
- For $`p=3,\ k=3`$, a candidate must satisfy $`\Delta=3`$; its common axial intersection has dimension $`b`$, and its central label restricts to a linear isomorphism from that intersection onto $`F`$. If $`|F|=p`$, this case is impossible too.
- The proof does not rule out the general $`k=2`$ branch. More precisely, every admissible $`s=p^r`$ above must have $`(R-1)^{s-1}x\notin T`$, where $`R`$ and $`x`$ are the physical action and lift defined below.

### Physical coordinates

The fixed-Frattini argument gives $`F\le Z(D)`$: each inverted generator has conjugation on $`F`$ equal to its inverse, hence trivial by odd order. In the purely axial case the $`p`$-power map is a homomorphism into $`F`$ (class two, odd $`p`$, and commutators elementary because $`N/F`$ has exponent $`p`$). Modulo $`F^p`$ the induced $`B`$-equivariant map from $`N/F`$ to $`F/F^p`$ is zero, since all weights are nontrivial and $`B`$ fixes $`F`$. Thus $`N^p\le F^p`$ and $`F=F^p[N,N]`$, giving $`F=[N,N]`$ and $`N^p=1`$. Strict cuts imply $`W\cap F=1`$, where $`W=H\cap N`$, by the centrality and core-freeness.

Use Lie coordinates on the class-two exponent-$`p`$ group $`N`$, where multiplication is vector addition plus half the commutator. Coprime decompositions give $`N=A_1\oplus A_2\oplus F`$, with zero cross-axis brackets, and sign identifies $`A_1,A_2`$ while fixing $`F`$. Work in the normalized setting $`B_2\le H`$. Since $`W`$ projects injectively, is additive/isotropic, and is stable under $`B_2`$, averaging gives
```math
W=\{(u,v,\ell(u)):u\in U_1,\ v\in U_2\}.
```
Here $`\ell:U_1\to F`$ is linear and $`U_2`$ is jointly isotropic for the actual central-valued bracket. A normalized actual top lift in $`N_H(B_2)`$ is $`g=(x,0,c)h`$, where the inverted lift $`h\in N_D(B)`$ has order $`p^k`$: its $`p^k`$-th power lies in $`C_N(B)=F`$ and is simultaneously fixed and inverted. The first axis action of $`h`$ is $`R`$; under the sign identification the second axis has action $`R^{-1}`$. Actual conjugation by $`g`$ on $`W`$ gives $`R U_1=U_1`$, $`R^{-1}U_2=U_2`$ on projection; inner $`N`$-conjugation acts trivially modulo $`F`$.

There are $`[D:C_D(t)]`$ marks, so sharpness gives $`|H|=|C_D(t)|=qp^{d+b}`$. The quotient of $`H`$ has order $`qp^k`$, hence $`\dim U_1+\dim U_2=\dim W=d+b-k`$. For $`u\in U_1\cap U_2`$ with $`\ell(u)=0`$, the element $`(u,-u,0)\in W`$ is inverted, hence equals a product of the two outside involutions $`(u,-u,0)t`$ and $`t`$. Avoidance forces $`u=0`$. Consequently
```math
\Delta=k-b+\dim(U_1\cap U_2)\le k.
```
For $`b=1`$ the intersection is actually trivial. The top-zero central phase formula (product with the two projected signs both $`t`$) gives all phases $`[u,A_1]`$ at vector $`(u,-u)`$. For nonradical $`u`$ this is all of $`F`$, impossible by avoidance. For the radical case, let $`P`$ be the intersection of $`U_2`$ with the joint bracket radical on the second axis. Its full preimage $`J`$ lies in $`Z(N)`$ and is normal in $`D`$, since $`P`$ is invariant under both axes and the top. The moving factor $`[J,B_2]`$ maps isomorphically onto $`P`$, by coprime averaging and because $`F`$ is fixed by $`B_2`$. As $`H\cap J`$ maps onto $`P`$ and is $`B_2`$-stable, averaging in that subgroup gives $`[H\cap J,B_2]=[J,B_2]`$. The moving factor is normal in $`D=N N_D(B)`$: $`N`$ centralizes it and $`N_D(B)`$ preserves $`J`$ and normalizes $`B_2`$. Core-freeness of $`H`$ forces $`P=0`$. Hence $`U_1\cap U_2=0`$ and $`\Delta=k-1`$ when $`b=1`$.

### Producing an actual collision

Let $`s=p^r`$ as in the statement. Since $`A/T`$ has dimension $`\Delta`$ and $`R`$ has $`p`$-power order, $`(R-1)^\Delta`$ kills $`A/T`$ (this includes $`\Delta=0`$). The first coordinate of the actual power $`g^s`$ is
```math
y=(1+R+\cdots+R^{s-1})x=(R-1)^{s-1}x;
```
the second is zero. If $`y\in T`$, write $`y=u+v`$ with $`u\in U_1`$, $`v\in U_2`$. Left multiplying $`g^s`$ by the actual $`W`$ element $`(-u,0,\ell(-u))`$ gives an element $`g_1=(v,0,c')h^s`$ in $`H`$. No condition is placed on the adjusted central coordinate $`c'`$, which incorporates the central BCH correction.

Now expand $`g_1^p`$ as the product of $`p`$ conjugates under $`h^s`$ followed by $`h^{ps}`$. These conjugates have only first-axis components $`R^{is}v`$ and the same central $`c'`$. All first-axis components lie in $`U_2`$ under sign identification. Thus their pairwise brackets vanish by joint isotropy, and the total central phase is $`pc'=0`$. Their sum $`a`$ lies in $`U_2`$, so actual left multiplication by $`(0,-a,0)\in W`$ produces
```math
(a,-a,0)h^{ps}\in H.
```
There is no cross-axis central correction. But this is $`((a,-a,0)t)(th^{ps})`$, both factors outside involutions by the axial sign and inversion of $`h`$. It is nonidentity already on the cyclic top because $`r+1<k`$. This proves an actual collision, not just a projected one; in particular it uses no fixed-point lifting modulo any radical.

Taking $`r=k-2`$, we have $`s-1\ge k`$ for $`p\ge5,\ k\ge3`$ or for $`p=3,\ k\ge4`$. When $`(p,k)=(3,3)`$ we instead have $`s-1=2`$, so only $`\Delta=3`$ survives. By the index formula this requires $`\dim(U_1\cap U_2)=b`$; injectivity gives the asserted isomorphism and the cyclic case has $`\Delta=2`$, as required.

## Provenance

Research revision `373ad83520f1c01675375c3826df51ec33196250`. Mira Cult directed the research; OpenAI models assisted with proof discovery and exposition. This addition has not received a separate full mathematical audit.
