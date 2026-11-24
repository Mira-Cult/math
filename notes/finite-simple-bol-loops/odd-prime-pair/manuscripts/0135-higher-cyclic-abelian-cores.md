# Sharp minimum orders for abelian cores with higher cyclic rotation

**Mira Cult**

In odd two-prime orders, the canonical rotation can have order greater than a prime. Here we determine the least loop order at every prescribed higher rotation among **abelian** canonical cores. An elementary core is excluded outright except for ternary order-nine rotation.

**Theorem.** Let a finite simple proper left Bol loop of order $`q p^a`$ have distinct odd primes $`p,q`$, canonical cyclic top of order $`n=p^k`$ with $`k\ge2`$, and abelian canonical $`p`$-core $`N`$, in the standard canonical reciprocal two-axis reduction. The reciprocal action requires $`n\mid q-1`$. Put $`f=\mathrm{ord}_q(p)`$ and $`d=\mathrm{lcm}(p^k,f)`$. Then:

1. Unless $`(p,k)=(3,2)`$, the first axial subgroup has exponent at least $`p^k`$, without a restriction on mixed weights. Thus the sharp minimum among **all abelian cores** is $`a=kd+k`$, already attained by the purely axial construction. Any mixed weight makes the order strictly larger, and equality has no $`B`$-fixed upper part and homocyclic axial parts of rank $`d`$.
2. For $`(p,k)=(3,2)`$, the sharp minimum among all abelian cores is $`a=d+3`$; any mixed weight makes the order strictly larger.
3. In particular no elementary abelian canonical core with top $`p^k`$ exists outside $`(p,k)=(3,2)`$, irrespective of axial and mixed packets or whether $`n`$ divides $`f`$.

The reciprocal two-axis and physical signed-folder inputs are stated in the [two-axis proof](../reviews/first-degree-prime-pair-upstream-necessity-audit.md), which includes the strict signed-normal cut used here. Write $`A^+`$ and $`A^-`$ for the fixed and inverted summands of a signed abelian group. The latter consists of elements sent to their negatives in additive notation. [Source and review scope](../VERIFICATION.md#higher-cyclic-abelian-cores).

## 1. Actual lift and the positive projection

Use the canonical faithful left group $`D`$, actual point stabilizer $`H`$, sign $`t`$, and inverted marks $`T`$. Let $`B=B_1B_2\cong C_q^2`$ be the sign-stable Sylow subgroup over the two axes, and $`D/N=B\rtimes C_n`$. The physical projected $`H`$ meets $`B`$ in $`B_2`$ and covers the top. Set $`C=C_N(B)`$, $`M=[N,B]`$. Coprime averaging for the abelian core gives the signed, rotation-stable decomposition
```math
N=A_1\oplus A_2\oplus V\oplus C,
```
where the $`A_i`$ move on their own axis alone and sign exchanges the two, and $`V`$ is the part moving on both. Thus $`M=A_1\oplus A_2\oplus V`$. The Frattini normalizer argument gives $`D=M\rtimes N_D(B)`$ and $`N_D(B)=B\rtimes S`$, for a sign-stable Sylow $`p`$-subgroup $`S`$ with $`S/C=C_n`$. Here $`B`$ is normal in its normalizer, $`N\cap N_D(B)=C`$, and the number of relevant Sylow $`p`$-subgroups is odd.

Take an inverted lift $`h\in S`$ of a generator of $`C_n`$ by sign displacement. The kernel of its action minus identity on $`C`$ is positive under sign: any negative element there would supply a central signed-normal order-$`p`$ subgroup disjoint from the core-free $`H`$, with equal physical orbit and sign index, forbidden by the strict signed-normal cut. Consequently $`h^n=1`$: its power lies in $`C`$, is fixed by $`h`$, and inverted by sign. Write $`R`$ for conjugation by $`h`$ on all of $`N`$, so $`tRt=R^{-1}`$.

Conjugate the actual $`H`$ so $`B_2\le H`$, using Sylow conjugacy inside $`NB_2`$, and remove its projected first-axis shift by sign-fixed diagonal $`B`$ conjugation as before. This does not require a based-folder equivalence: the outside involution class and its square are conjugacy-invariant in the signed group, so physical cut and avoidance facts persist. Put $`W=H\cap N`$. Sylow conjugacy in $`H\cap NB`$ gives $`H=W N_H(B_2)`$. A lift of $`hN`$ in $`N_H(B_2)`$, after dropping its $`B_2`$ factor, has the form $`a_0 h`$ where $`a_0\in C_N(B_2)=A_1\oplus C`$. Indeed the moving coordinate of an element normalizing $`B_2`$ must centralize it, since $`B_2`$ embeds in $`D/N`$. The actual $`W`$ is stable under $`R`$ because this lift acts by $`R`$ on abelian $`N`$.

For later use $`W`$ maps onto $`C=N/M`$. Indeed $`H`$ normally generates $`D`$: sending each loop point to its translation modulo the normal closure of $`H`$ defines a surjective homomorphism to the resulting group quotient, which is trivial by nonassociative simplicity. Therefore $`H`$ surjects onto the finite $`p`$-group $`D/(MB)=S`$, and $`W`$ surjects onto its kernel $`C`$ over the top, by taking a Sylow $`p`$-subgroup of $`H\cap NB`$. Averaging $`W`$ under $`B_2`$ places these representatives in $`W\cap(A_1\oplus C)`$. The subgroup $`W\cap C`$ is normal in $`D`$ since it is invariant under $`R`$, centralized by $`B,N`$ and lies in the top normalizer. Core-freeness gives $`W\cap C=0`$. Thus $`W\cap(A_1\oplus C)`$ is the graph of an onto additive map from a subgroup of $`A_1`$ to $`C`$. This also shows $`A_1\ne0`$: otherwise $`C=0`$, the actual lift $`a_0h`$ is $`h`$, and a nonidentity inverted mark lies in $`H`$.

Because $`p`$ is odd, $`N=N^+\oplus N^-`$ under $`t`$, and $`\operatorname{pr}_+=(1+t)/2`$ is a group projection. Its restriction to $`W`$ is injective, since a nonzero element of $`W\cap N^-`$ would already be an inverted mark in $`H`$. Counting the outside involution class by coprime lifting gives $`[D:H]=q p^k |N^-|`$, whereas the actual projected stabilizer has index $`q`$ in $`D/N`$, giving $`[D:H]=q[N:W]`$. Consequently the positive quotient
```math
P=N^+/\operatorname{pr}_+W
```
has exact order $`p^k`$. Put $`Z=R-R^{-1}`$. It anticommutes with $`t`$ and $`W`$ is stable under it. Thus $`Z^2`$ acts on $`P`$, because it preserves both sign spaces and commutes with $`\operatorname{pr}_+`$. Both $`p`$ and $`Z^2`$ are commuting nilpotent endomorphisms of $`P`$; $`R`$ has $`p`$-power order and reduction modulo $`p`$ makes it unipotent. Any product of $`k`$ factors from these two endomorphisms kills $`P`$, since every nonzero intermediate image strictly decreases in order. This argument works for any abelian $`N`$.

## 2. All mixed elementary models are excluded outside the exception

Write $`s=p^{k-1}`$. The actual stabilizer contains
```math
(a_0 h)^s=(\Sigma_s(R)a_0)h^s,\qquad \Sigma_s(X)=1+X+\cdots+X^{s-1}.
```
If the positive projection of the vector component lies in $`\operatorname{pr}_+W`$, cancel a matching actual $`w\in W`$ on the left. This leaves $`v h^s\in H`$ with $`v\in N^-`$. But $`v h^s=(v t)(t h^s)`$ is a product of two outside involutions, hence lies in the square of their unique conjugacy class. This square avoids $`H`$ off identity. Since $`h^s`$ projects nontrivially to the top, this is impossible. It is important that the remaining vector need only be sign-negative, not zero.

If $`N`$ is elementary then $`\Sigma_s(R)=(R-1)^{s-1}`$. The operator $`Z`$ equals $`(R-1)(1+R^{-1})`$, with commuting invertible second factor, so the image of this norm is $`Z^{s-1}N`$. Since $`s-1`$ is even, its positive projection is contained in $`(Z^2)^{(s-1)/2}N^+`$. If $`s-1\ge2k`$ this projects to zero in $`P`$, giving the collision just proved impossible. For odd $`p`$ and $`k\ge2`$, $`s-1\ge2k`$ except $`(p,k)=(3,2)`$. This uses no mixed character count.

## 3. The same projection forces the full axial exponent in the abelian case

Suppose the exponent of $`A_1`$ divides $`p^{k-1}`$. Then the same holds for $`A_2`$ and $`C`$ (the onto graph above). Thus $`D_0=A_1\oplus A_2\oplus C`$ is a signed, rotation-stable abelian subgroup of exponent dividing $`p^{k-1}`$ containing $`a_0`$. Let $`P_0\le P`$ be the image of $`D_0^+`$; it is stable under $`p,Z^2`$ and has exponent at most $`p^{k-1}`$.

Expand the geometric sum about $`R=1`$:
```math
\Sigma_s(R)=\sum_{i=0}^{s-1}\binom{s}{i+1}(R-1)^i .
```
The coefficient valuation is $`u=k-1-r`$, $`r=\nu_p(i+1)`$, by $`\binom{s}{i+1}=s\binom{s-1}{i}/(i+1)`$ and the nonzero Lucas digits of $`\binom{s-1}{i}\bmod p`$. If $`r=0`$ the term vanishes on $`a_0`$ by exponent. For every other term, $`p^u (R-1)^iD_0=p^u Z^i D_0`$. Its positive projection lies in $`p^u(Z^2)^{\lfloor i/2\rfloor}D_0^+`$: factor the even power, and then take the sign-positive component of the remaining vector. This vanishes in $`P`$ if $`u+\lfloor i/2\rfloor\ge k`$.

For $`p\ge5`$ and $`r\ge1`$, $`i\ge p^r-1\ge2r+2`$, so all terms vanish in $`P`$. For $`p=3`$, the same inequality holds except $`i=2,r=1`$. If $`k\ge3`$, this term is killed as well: $`3^{k-2}P_0`$ has order at most three, since $`P_0`$ has order at most $`3^k`$ and exponent at most $`3^{k-1}`$, and two cyclic factors of that largest exponent would exceed its order. A nilpotent endomorphism $`Z^2`$ on this at-most-order-three group is zero. Thus $`3^{k-2} Z^2 P_0=0`$. In each nonexceptional case the vector of the genuine lift power has positive projection zero in $`P`$, giving the forbidden product of outside involutions. Therefore $`\exp(A_1)\ge p^k`$.

## 4. Sharp order and the ternary exception

The deepest nonzero axial layer, for $`\exp(A_1)=p^e`$, is an elementary space with nonzero Frobenius/top weight orbit of size $`d`$. Every other $`p`$-power layer surjects onto it by multiplication by a suitable power of $`p`$. Hence $`|A_1|\ge p^{ed}`$. The sign-negative group of a matched axis pair has size $`|A_1|`$, so nonexceptionally the actual index gives $`a\ge kd+k`$. A nonzero mixed part has nonzero negative sign space already modulo $`p`$, because the top and its reciprocal weights give the mixed orbit bound; coprime sign lifting gives a nonzero contribution on the actual mixed group. At equality, $`C^-=0`$ and there is no mixed part. Sign then acts trivially on $`C`$ and conjugates the rotation on $`C`$ to its inverse, so that odd-order rotation acts trivially. The quotient $`D/(MB)=C\times C_n`$ is generated by inverted marks, hence $`C=0`$. Equality in the layer counts gives precisely $`d`$ cyclic factors of order $`p^k`$ on each axis. The [induced augmentation construction](higher-top-augmentation-construction.md) attains the bound.

For $`(p,k)=(3,2)`$, the axial part still contributes at least $`d`$, and a mixed packet would add at least $`f(9-1)/2=4f`$ negative dimensions modulo $`p`$ by the [mixed packet count](elementary-higher-top-mixed-weight-lower-bound.md); hence in the presence of mixed weights $`a\ge d+2+4f>d+3`$. In the purely axial case, an axial subgroup of exponent at least nine gives $`a\ge 2d+2>d+3`$. Otherwise the two axes are elementary. If $`a=d+2`$, then $`C^-=0`$, so the argument above gives $`C=0`$. Coprime averaging under $`B_2`$ splits $`W`$ into its two axis intersections. The second intersection is normal in $`D`$, since it is stable under $`B_2,R`$ and centralized by $`B_1,N`$; hence it is zero by core-freeness. Now $`K=W\le A_1`$ has index nine by the mark count, and $`(R-1)^2A_1\subseteq K`$ by nilpotence on the two-dimensional quotient. Cubing the true lift gives vector $`(R-1)^2x\in K`$ over $`h^3`$. Canceling that vector leaves the forbidden nonidentity inverted $`h^3`$. Hence $`a\ge d+3`$. The [induced order-nine construction](higher-top-augmentation-construction.md#the-ternary-order-nine-minimum) attains this bound for every admissible pair. No construction of a larger abelian loop with mixed weights, or exclusion of a smaller nonabelian loop, follows.

## Examples and remaining questions

For $`p=5,q=101,n=25`$, the order of $`5`$ modulo $`101`$ is $`25`$, and the least abelian-core order with this rotation is $`101\cdot5^{52}`$. For $`p=3,q=73,n=9`$, the order of $`3`$ modulo $`73`$ is $`12`$, so $`d=36`$ and the least order is $`73\cdot3^{39}`$. The latter example uses the induced construction rather than the single-field order-nine construction.

The minimum is taken over abelian cores at a fixed cyclic top, not over all possible cores or rotation groups. This proof identifies the equality structure away from ternary order nine, but it is not an isomorphism or isotopy census. In the nonabelian branch, the projected stabilizer need not retain sharp avoidance; the [Frattini quotient result](0131-frattini-quotient-crowding.md) explains that distinction.
