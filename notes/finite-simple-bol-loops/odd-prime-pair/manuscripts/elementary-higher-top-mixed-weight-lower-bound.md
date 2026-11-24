# Elementary higher cyclic tops require mixed weights

**Historical bound.** The [later positive-projection obstruction](0135-higher-cyclic-abelian-cores.md) excludes these higher-top elementary cores outright outside ternary order nine. This earlier weight calculation is retained as a proof dependency and for its original scope.

**Research proof; see the scope of verification.** [Verification and provenance](../VERIFICATION.md).

**Corollary.** Let a finite simple proper left Bol loop have order $`p^a q`$ for distinct odd primes with elementary abelian canonical $`p`$-core and cyclic canonical top of order $`p^k`$, $`k\ge2`$. Apart from $`(p,k)=(3,2)`$, its canonical $`p`$-core has a mixed weight for the two $`q`$-axes. With $`f=\mathrm{ord}_q(p)`$, necessarily
```math
a\ \ge\ k+\frac{f(p^k-1)}2.
```

This makes no parity restriction on $`f`$.

For clarity, the split architecture used in the axial no-go theorem is forced here if no mixed weight exists. Take the sign-stable Sylow $`q`$-group $`B`$ over the two-axis normal subgroup of the canonical quotient. Elementary $`N`$ decomposes by coprime action as $`N=M\oplus C`$, where $`M=[N,B]`$ and $`C=C_N(B)`$. If there are only axial nontrivial weights, $`M=A_1\oplus A_2`$ with each axis fixed-point-free on its part and trivial on the other; the sign exchanges the parts. (The $`B`$-action is not wholly trivial by Fitting self-centralization.) The Frattini normalizer argument gives $`D=N L`$, $`L=N_D(B)`$, and $`N\cap L=C`$: an element of $`N`$ normalizing $`B`$ acts trivially on the isomorphic image of $`B`$ in $`D/N`$. Thus $`D=M\rtimes L`$. The group $`B`$ is normal in $`L`$, and a sign-stable Sylow $`p`$-group $`S`$ of $`L`$ gives $`L=B\rtimes S`$ with $`S/C`$ the prescribed cyclic top. Its existence follows by oddness of the number of Sylow $`p`$-subgroups. These are exactly the hypotheses of the no-go theorem, whose central-line argument proves the splitting within $`S`$ rather than assumes it. Therefore a mixed weight is necessary away from the indicated ternary exception.

The simultaneous top and Frobenius orbit of a mixed weight $`(a_0,b_0)`$ has $`p^k f`$ elements: in $`(\alpha^i p^j a_0,\alpha^{-i}p^j b_0)`$ the ratio determines $`i\bmod p^k`$, then either coordinate determines $`j\bmod f`$. Here $`\alpha`$ has order $`p^k`$ modulo $`q`$. At most $`f`$ of these weights are fixed by the sign's coordinate swap, since the equality of coordinates fixes at most one $`i`$. Thus the signed orbit, or its union with an exchanged orbit, contributes at least $`f(p^k-1)/2`$ negative dimensions. This count is valid with arbitrary weight-space multiplicities: two exchanged spaces contribute their common dimension, and each has multiplicity at least one. As the actual sign budget on the core is $`s=a-k`$, the claimed bound follows.

In particular, for $`p^k\mid f`$, the attempted arbitrary-top exponent $`a=f+k+(p^{k-1}-1)/2`$ is impossible for **any** such elementary-core loop except the ternary top-nine case. Indeed, after subtracting $`k`$, the strict inequality to the new bound is equivalent to $`f(p^k-3)>p^{k-1}-1`$, which follows from $`f\ge p^k\ge9`$. This strengthens rejection of the particular incomplete transversal, without excluding models with a non-elementary core at those orders.


## The actual stabilizer also forces an axial packet

A separate sharpening, with the preceding source at `a636051a` left intact, is that every elementary-core case also has an axial packet. In fact suppose $`C_N(B_2)=C_N(B)=C`$. Put $`M=[N,B]`$, $`N=M\oplus C`$ and $`L=N_D(B)`$. For the orbit and avoidance argument arrange $`B_2\le H`$ by coprime conjugacy. The physical $`W=H\cap N`$ surjects onto $`C=N/M`$: the actual $`H`$ normally generates $`D`$ and hence covers its $`p`$-group quotient $`D/(MB)`$, and a Sylow $`p`$-group of $`H\cap NB`$ covers the kernel $`N/M`$ of projection to the cyclic top. The coprime $`B_2`$-average on the $`B_2`$-stable $`W`$ puts every such $`C`$ coordinate in $`W\cap C_N(B_2)=W\cap C`$. Thus $`C\le W`$.

Also $`N_D(B_2)=L`$: write an element of $`D`$ as $`n\ell`$, $`\ell\in L`$ already preserving both axes; a normalizing $`n\in N`$ lies in $`C_N(B_2)=C`$, because $`B_2`$ embeds in $`D/N`$. The actual stabilizer $`H=W N_H(B_2)`$ therefore has $`H\cap L`$ covering the cyclic top. Since $`C\le H\cap L`$, that subgroup contains a full Sylow $`p`$-group of $`L`$. A conjugate of it is sign-stable, and a sign displacement of a lift of any top generator is a nonidentity inverted mark in it. This contradicts sharp transitivity. Hence $`C_N(B_2)>C_N(B)`$, which is exactly an axial weight in the split two-axis action.

For $`k\ge2`$ and $`(p,k)\ne(3,2)`$ the two distinct contributions therefore coexist. The physical negative dimension from the axial packet and its sign-mate is at least $`\mathrm{lcm}(p^k,f)`$; their supports are disjoint from every mixed packet. Add the mixed lower bound to obtain
```math

a\ \ge\ k+\mathrm{lcm}(p^k,f)+\frac{f(p^k-1)}2.
```

This sharper inequality still has elementary-core scope only. The argument does not exhibit a stabilizer supporting the needed coupling between the two weight regimes, or prove that any larger exponent is attained.
