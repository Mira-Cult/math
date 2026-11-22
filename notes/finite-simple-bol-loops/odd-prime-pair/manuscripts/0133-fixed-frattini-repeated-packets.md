# Repeated axial packets and physical stabilizer phases

**Mira Cult**

Use the signed folder and normalization from [Frattini quotient crowding (0131)](0131-frattini-quotient-crowding.md) and the packet and joint-radical definitions from [the multiplicity-one analysis (0132)](0132-fixed-frattini-multiplicity-one.md). See the [verification record](../VERIFICATION.md) for the proof-review scope.

Retain purely axial weights, nonabelian $`N`$, pointwise sign-fixed $`F=\Phi(N)`$ and cyclic top $`p^k`$ with $`k\ge2`$, but allow arbitrary packet multiplicities and modular extensions within a packet.

Put $`D_0=\mathrm{lcm}(p^k,\mathrm{ord}_q(p))`$, $`b=\log_p|F|`$, and let $`m`$ be the sum of packet multiplicities per axis. Work in the even character-degree case where every packet is self-dual. For each packet $`i`$ let $`m_i`$ be its multiplicity, $`j_i`$ the dimension of its joint radical divided by $`D_0`$, and $`r_i`$ the rank of a chosen scalar commutator contraction divided by $`D_0`$. Then
```math
D_0\sum_i\left(j_i+r_i+\frac12(r_i\bmod 2)\right)\le mD_0+k-b.
```

Indeed every invariant subspace in one packet has dimension a multiple of $`D_0`$: over a splitting field, split it into its intersections with the weight spaces using coprime projections, and use top and Frobenius to equate the dimensions of these intersections over the transitive orbit. This works without semisimplicity for the top. Apply this to both radicals and to the physical moving stabilizer packet components, which exist since the sums of rational $`q`$-weight spaces in distinct packets are disjoint and top-stable. The cross-packet scalar pairing vanishes, as each orbit is self-dual.

The physical $`U_2`$ has zero intersection with the joint radical also at arbitrary multiplicity. Its intersection there is a $`B_2`$- and top-stable subspace, and any nonzero such subspace has a full preimage $`J\le Z(N)`$ whose unique $`B_2`$-moving lift $`[J,B_2]`$ is contained in $`H`$ by coprime decomposition on $`H\cap J`$. The latter surjects onto the considered intersection by definition of $`U_2`$. The moving lift is normal in the faithful group, as in the preceding proof, contradicting core-freeness. Now on packet $`i`$, project the moving stabilizer to the quotient by its joint radical, without loss of dimension. The scalar form has dimension $`(m_i-j_i)D_0`$ and rank $`r_iD_0`$ there. Ordinary isotropy and the multiple-of-$`D_0`$ constraint bound its dimension by $`(m_i-j_i-\lceil r_i/2\rceil)D_0`$. On the whole first axis use ordinary isotropy without rounding, giving $`(m-\sum_i r_i/2)D_0`$. No packetwise splitting is imposed on the first-axis stabilizer. The genuine physical stabilizer has dimension $`mD_0+b-k`$. Summing yields the claim.

If one contraction is nondegenerate on the quotient by the joint radical on every packet (i.e. $`r_i=m_i-j_i`$), then $`b\le k`$ and every nonradical quotient multiplicity is even: an odd one would imply $`D_0/2\le k-b`$, impossible. In particular this applies automatically when $`|F|=p`$, where any nonzero scalar contraction has exactly the joint radical. Thus the cyclic-Frattini repeated branch cannot have any packet with odd nonradical multiplicity, including an isolated rank-one packet in a larger repeated envelope. This does not rule out configurations with all residual multiplicities even or with no common full-rank contraction.


<a id="physical-phases"></a>

## Physical stabilizer constraints in the all-even packet case

We now impose the physical avoidance condition, beyond the dimension count.

Keep the hypotheses of that bound and suppose one scalar contraction is nondegenerate modulo the entire joint radical. Write $`m`$ for the total multiplicity on one axis, $`j`$ for its joint radical multiplicity, and continue to use $`D_0,b,k`$. The joint-radical quotient multiplicities are all even and $`b\le k`$. In fact the moving stabilizer uses the maximum possible dimension $`(m-j)D_0/2`$ and uses half of each packet's radical quotient. Indeed ordinary whole-first-axis isotropy bounds $`\dim U_1\le (m+j)D_0/2`$, the rounded moving bound gives $`\dim U_2\le(m-j)D_0/2`$, and the sum of the two deficits is exactly $`k-b`$ by the physical dimension $`mD_0+b-k`$. But the moving deficit is a multiple of $`D_0>k`$, so is zero, packet by packet. Thus its image in the nondegenerate quotient is Lagrangian for the chosen scalar contraction and is jointly isotropic for every contraction. The first-axis deficit is exactly $`k-b`$.

There is also a precise additional top-zero avoidance test on the central lift of these subspaces. The pointwise sign-fixed Frattini subgroup $`F`$ is central and the core has exponent $`p`$ by the [previous argument](0132-fixed-frattini-multiplicity-one.md#averaging). Use the class-two Lie coordinates on $`N`$ (additive law obtained from group multiplication by subtracting half the central commutator). The coprime two-axis decomposition is $`A_1\oplus A_2\oplus F`$ in these additive coordinates; sign exchanges the axes, identified via sign, and fixes $`F`$. The physical $`W=H\cap N`$ is additive and isotropic since $`[W,W]\le W\cap F=1`$. In the normalization with $`B_2\le H`$, it has the form
```math
W=\{(u,v,\ell(u)):u\in U_1,\ v\in U_2\}
```
for a prime-field linear map $`\ell:U_1\to F`$. Indeed $`W`$ projects injectively modulo $`F`$, is stable under $`B_2`$, and coprime averaging splits off its $`B_2`$-moving part, which has zero $`F`$ coordinate.

Then avoidance of nonidentity outside-involution products at identity projection in $`D/N`$ imposes more than injectivity of $`\ell|_{U_1\cap U_2}`$. The two projected outside involutions above identity coincide, and the projected $`H=B_2\rtimes C_{p^k}`$ conjugates every quotient outside involution to the sign: the top controls its top displacement (doubling is invertible), and $`B_2`$ controls the antidiagonal displacement. Lift that conjugation using actual $`H`$ to preserve $`W`$. Two outside involutions projecting to the sign have form $`xt,yt`$ with $`x,y\in N^-`$ in additive Lie coordinates. A product in $`W`$ can have arbitrary central component from half the bracket of their vector parts, so checking $`W\cap N^-`$ alone is in general insufficient. More precisely, if their additive vector sum has first coordinate $`u`$, the central part ranges over the commutator image $`[u,A_1]`$: write the two negative vectors as $`(s,-s,0)`$ and $`(u-s,-(u-s),0)`$ after absorbing the inversion of the second into its free parameter. Cross-axis commutators vanish, and sign fixes the central bracket, so the half bracket of the two negative vectors is exactly $`[s,u]`$ in the identified first-axis form. Thus the exact test is
```math
\ell(u)\notin [u,A_1]\quad\text{for every nonzero }u\in U_1\cap U_2.
```
For zero $`u`$ the same bracket is zero, so there is no further collision. Injectivity of the restriction of $`\ell`$ is necessary. It suffices when the intersection is joint radical; beyond the radical the displayed test requires avoiding each individual bracket image, not merely avoiding zero. When $`|F|=p`$, any nonradical $`u`$ has $`[u,A_1]=F`$, so the test forces a radical intersection. But $`U_2`$ avoids the joint radical by core-freeness. Consequently in the cyclic-Frattini branch the two physical axial subspaces must be disjoint under sign identification, not merely meet in dimension at most one.

This does not establish avoidance at nonzero top or exclude the resulting transverse Lagrangian candidates. It isolates the genuine central product term that survives Frattini projection.


## Phase variation at nonzero top

Under the same hypotheses choose a sign-inverted top lift $`h`$ normalizing $`B`$, of order $`p^k`$: its $`p^k`$th power is in the central positive $`F`$ (the $`B`$-fixed part of $`N`$), and is inverted, so is trivial. In the normalized physical stabilizer choose the actual lift $`(x,0,c)h`$ using the $`B_2`$-normalizer; $`B_2`$-fixed Lie coordinates have no second-axis coordinate. Let $`R`$ be the action of $`h`$ on the first axis. For a product with top $`j`$ normalize its projected inverting outside signs to $`t,h^{-j}t`$: first remove the $`B_2`$-shift of the product by actual $`B_2`$ conjugation, then use powers of the actual stabilizer lift to move the first outside top exponent to zero; its top changes by twice the step. The two negative vector graphs in the resulting product are $`(s,-s,0)`$ and $`(y,-R^{-j}y,0)`$. Both lifts have zero central coordinate since the corresponding signs fix $`F`$.

For fixed first and second totals $`(d,a)`$, a solution exists exactly when $`d+a\in(R^j-1)A_1`$. Given one choice of $`s,y`$, the full set of solutions changes $`s`$ by $`z\in C_{A_1}(R^j)`$ and $`y`$ by $`-z`$. The central coordinate of the product is
```math
\tfrac12\left([s,y]+[s,R^{-j}y]\right)=\tfrac12[s,d-a].
```
Thus its attainable values form one affine coset of $`\tfrac12[C_{A_1}(R^j),d-a]`$ (the bracket notation here means the image of the indicated linear pairing with the fixed vector). For cyclic $`F`$ this image is all of $`F`$ or zero. In that case let $`J`$ be the joint radical of the first-axis alternating form. Subject to the fixed-point lifting hypothesis below, the image is all of $`F`$ precisely when the image of $`a`$ in $`A_1/J`$ is outside $`(R^j-1)(A_1/J)`$. To justify using fixed vectors from the full module, the annihilator of $`C_{A_1}(R^j)`$ in the nondegenerate quotient need not in general be the image of $`R^j-1`$ on that quotient unless fixed points lift modulo $`J`$. Accordingly this last criterion holds **when** $`C_{A_1}(R^j)`$ surjects onto $`C_{A_1/J}(R^j)`$, for instance when $`J=0`$ or splits off as an $`R`$-module. Without that extra hypothesis use the exact bracket-image condition above. Under the hypothesis, invariance and nondegeneracy identify the fixed-space annihilator with that image, and $`d+a\in(R^j-1)A_1`$ makes $`d-a`$ congruent to $`-2a`$ there. In the full-image case, any projected solution in the stabilizer fiber lifts to a genuine forbidden collision, regardless of its central phase.
