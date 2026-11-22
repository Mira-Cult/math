# Central Frattini cores with multiplicity-one axial packets

**Mira Cult**

The signed folder, two-axis notation and Frattini reduction are defined in [Frattini quotient crowding (0131)](0131-frattini-quotient-crowding.md). See the [verification record](../VERIFICATION.md) for the proof-review scope.


<a id="rank-bound"></a>

## The multiplicity-free central Frattini rank obstruction

Use the canonical two-axis hypotheses, with $`F=\Phi(N)`$ fixed pointwise by the canonical sign and $`N`$ nonabelian. Suppose $`N/F=A_1\oplus A_2`$ has only axial weights, and on each axis the simultaneous top/Frobenius packets have multiplicity one. Write $`d=\dim A_1=\dim A_2`$, $`b=\log_p|F|`$, and $`p^k`$ for the top order. For any prime-field linear functional on $`\Omega_1(F)`$, let $`r`$ be the rank of its alternating commutator contraction on one axis, and let $`r_{\rm sd}`$ be the sum of ranks on the self-dual packets of that axis. Then
```math
r+r_{\rm sd}/2\le d+k-b .
```
In particular an everywhere nondegenerate contraction supported on self-dual packets excludes the branch for $`k\ge2`$: it would imply $`d/2\le k-b`$, whereas $`d\ge p^k>2k`$.

As in the predecessor, $`F`$ is central in $`D`$, since inverted generating marks act on the pointwise sign-fixed $`F`$ by automorphisms equal to their own inverses and of odd order. Thus $`H\cap F=1`$, the physical Frattini stabilizer $`U=(H\cap N)F/F`$ has dimension $`d+b-k`$, and is isotropic for every commutator contraction. The contraction takes values via $`\Omega_1(F)`$, since commutators are central and $`p`$th powers belong to $`F`$. The pairing between the two axes is zero: invariance under the first $`q`$-axis, acting trivially on the second and fixed-point-freely on the first, forces this. Sign exchanges the forms on the two axes, so they have the same ranks and packet types.

Normalize the physical stabilizer to contain $`B_2`$ as in the predecessor. Averaging over $`B_2`$ decomposes $`U=U_1\oplus U_2`$ with $`U_i\le A_i`$. The moving summand $`U_2`$ is invariant under the actual top lift on the quotient and under $`B_2`$. Over a splitting field its subspace is a sum of weight lines by multiplicity one, and its support is stable under top and field Frobenius. Consequently $`U_2`$ consists of entire packets, not an arbitrary isotropic subspace.

Invariance pairs weight $`\chi`$ only with $`\chi^{-1}`$. Thus the blocks of the form are isolated self-dual packets and reciprocal pairs of distinct packets; packets with absent dual are radical. On a self-dual packet a nonzero contraction is nondegenerate by irreducibility. Between a reciprocal pair the pairing is either zero or perfect, again by irreducibility. For $`U_2`$, an active self-dual packet is forbidden in its entirety. In an active reciprocal pair, $`U_2`$ can contain at most one of its two perfectly paired packets; they have equal dimensions. Therefore
```math
\dim U_2\le d-r_{\rm sd}-(r-r_{\rm sd})/2.
```
On $`U_1`$ use only ordinary isotropy, giving $`\dim U_1\le d-r/2`$. Summing these bounds and substituting the genuine physical dimension of $`U`$ gives the inequality.

No statement is made here for repeated packets (where top-invariant isotropic graphs can occur), mixed weights, or sign-moving Frattini subgroups. This rank bound is necessary, not a sufficiency test for physical folders.


<a id="averaging"></a>

## Averaging forces radical packets in the self-dual fixed-Frattini branch

Keep the multiplicity-one axial hypotheses of the rank bound.

Put $`f=\mathrm{ord}_q(p)`$, $`D_0=\mathrm{lcm}(p^k,f)`$, and let $`m`$ be the number of packets on one axis. All packets have dimension $`D_0`$: on the nonzero character indices modulo $`q`$, Frobenius and the canonical top act by multiplication by $`p`$ and a scalar of order $`p^k`$, respectively. Their generated subgroup in the cyclic group $`\mathbb F_q^\times`$ has order $`D_0`$ and acts freely on those indices. A packet is self-dual precisely when inversion of its characters, i.e. negation of its indices, preserves that orbit. This is equivalent to $`-1`$ belonging to the generated subgroup, hence to even $`f`$ since the top has odd order.

Suppose $`f`$ is even, and let $`z=\dim_{\mathbb F_p}\Omega_1(F)\ge1`$, $`b=\log_p|F|`$. Say that a packet is joint radical if its entire commutator pairing is zero. Different packets pair trivially because each is self-dual and no two are the same. If $`h`$ of the $`m`$ packets are not joint radical, then
```math
h\le\left\lfloor \frac{L}{\rho}\right\rfloor,\qquad
L=\left\lfloor\frac{2(mD_0+k-b)}{3D_0}\right\rfloor,\qquad
\rho=\frac{(p-1)p^{z-1}}{p^z-1}.
```
Indeed a nonzero contraction acts nondegenerately on each packet on which it is nonzero, by irreducibility and the central commutator target. Since every packet is self-dual, if it is active on $`a`$ packets the preceding rank inequality gives $`a\le L`$. Choose a contraction uniformly among nonzero linear functionals on $`\Omega_1(F)`$. For every nonradical packet its commutator image contains a nonzero vector, which is detected by exactly $`(p-1)p^{z-1}`$ among the $`p^z-1`$ eligible functionals. Hence the expected number active is at least $`\rho h`$, proving the claim.

In particular a joint radical packet is compulsory. Indeed $`\rho>1-1/p\ge2/3`$. If $`h=m`$, some contraction has $`a>2m/3`$, so $`3a/2-m\ge1/2`$ by integrality. The rank inequality would force $`D_0/2\le k-b`$, impossible since $`D_0\ge p^k>2k`$. The displayed quantitative bound forces at least $`m-\lfloor L/\rho\rfloor`$ joint radical packets on each axis, and sign matches them. This does not assume that any single contraction simultaneously detects every nonzero commutator image.

The radical does give an actual signed-normal, central-in-$`N`$ elementary subgroup; this does not justify stripping it to retain a sharp folder. For detail, take the preimage $`J`$ of the joint radical of the full commutator pairing; it is characteristic relative to this pairing and equals $`Z(N)`$, since $`F`$ is central. It is abelian and $`[J,B]`$ maps isomorphically to the joint radical in $`N/F`$: coprime decomposition gives $`J=[J,B]\times C_J(B)`$ and $`F\le C_J(B)`$, while the quotient radical has no trivial $`B`$-weight. In particular $`[J,B]`$ is elementary. It is invariant under the actual $`B`$-normalizer and sign, and central in $`N`$, hence normal in $`D=N N_D(B)`$. If nontrivial its strict cut forces quotient mark multiplicity greater than one by the [Frattini crowding law](0131-frattini-quotient-crowding.md); the usual sharp avoidance therefore does not descend by simply projecting the original marks and stabilizer.


## The core has exponent $`p`$

This follows already under the predecessor's purely axial hypotheses, without the averaging assumptions. The group $`F`$ is central, and every commutator in $`N`$ has order dividing $`p`$. Since $`p`$ is odd, the class-two power formula makes $`x\mapsto x^p`$ a homomorphism into $`F`$. Modulo $`F^p`$ it induces an equivariant linear map $`N/F\to F/F^p`$. The target is fixed by the $`q`$-axes and every source weight is nontrivial on one of them; coprime averaging makes the map zero. Thus $`N^p=F^p`$, and the Frattini identity yields $`F=F^p[N,N]`$. Since $`F`$ is a finite abelian $`p`$-group this implies $`F=[N,N]`$ (in the quotient by $`[N,N]`$, raising to $`p`$ cannot be surjective unless the quotient is trivial). Hence $`F`$ is elementary abelian, $`N^p=1`$, and $`z=b`$. In the even-$`f`$ multiplicity-free case the packet bracket images on one axis span $`F`$: cross-axis and cross-packet brackets vanish, and sign exchanges the axes while fixing $`F`$ pointwise.


<a id="core-freeness"></a>

## Core-freeness closes the self-dual multiplicity-free fixed-Frattini branch

The entire multiplicity-one branch is impossible for even $`f`$ and $`k\ge2`$.

Let $`F=\Phi(N)`$, let $`D_0=\mathrm{lcm}(p^k,f)`$ be the size of each packet, and let $`m`$ be the number of packets per axis. As in the preceding notes $`F`$ is central in the faithful group $`D`$, $`H\cap F=1`$, and the physical stabilizer image $`U`$ in $`N/F`$ has dimension $`mD_0+b-k`$, where $`b=\log_p|F|`$. With actual $`B_2\le H`$ the moving part $`U_2`$ consists of entire second-axis packets, and the fixed part $`U_1`$ lies in the first axis.

The new point is that $`U_2`$ cannot contain a joint-radical packet $`P`$. Indeed its full preimage $`J`$ in $`N`$ lies in $`Z(N)`$ by definition of the joint commutator radical, and is normal in $`D`$: $`P`$ is invariant under the two axes, the top and inner action of $`N`$ on $`N/F`$. On the abelian group $`J`$ apply coprime $`B_2`$ decomposition. Its moving factor $`J_m=[J,B_2]`$ maps isomorphically onto $`P`$, since $`F`$ is fixed by $`B_2`$ and $`B_2`$ acts fixed-point-freely on $`P`$. As $`H\cap J`$ covers $`P`$ if $`P\le U_2`$, coprime decomposition on that $`B_2`$-invariant subgroup shows $`[H\cap J,B_2]=J_m`$. Now $`J_m`$ is normal in $`D`$: it is centralized by $`N`$ and is invariant under $`N_D(B)`$, which preserves $`J`$ and normalizes the axis $`B_2`$ (the top acts by its reciprocal scalar). Since $`D=N N_D(B)`$, the nontrivial $`J_m`$ is a normal subgroup contained in $`H`$, contradicting core-freeness. This forbids the radical packet *in the stabilizer*; no sharpness claim is made for a quotient by it.

When $`f`$ is even, all packets are self-dual, so they pair only with themselves. Let $`h`$ be the number of joint-nonradical packets per axis; $`h>0`$ since $`N`$ is nonabelian and cross-axis brackets vanish. For one scalar contraction let $`a`$ of those packets be active. In addition to the joint radical exclusion above, $`U_2`$ cannot contain an active packet because the contraction is nondegenerate there. Hence
```math
\dim U_2\le(h-a)D_0,\qquad \dim U_1\le mD_0-aD_0/2,
```
the latter by ordinary alternating-form isotropy. Comparing with the physical dimension gives $`(3a/2-h)D_0\le k-b`$. But a random nonzero contraction is active on each nonradical packet with probability strictly greater than $`1-1/p\ge2/3`$, by the finite functional count in the averaging deduction. Some contraction therefore has $`a>2h/3`$, so $`3a/2-h\ge1/2`$ by integrality. This implies $`D_0/2\le k-b`$, impossible since $`D_0\ge p^k>2k`$.

For odd $`f`$, reciprocal packet pairs need not be jointly excluded: isotropy may allow one of an active reciprocal pair. The argument makes no exclusion in that case, or for repeated or mixed packets or sign-moving Frattini subgroups.


## A separate constraint for reciprocal packets

In the same multiplicity-one purely axial model with odd $`f`$, let $`h`$ be the number of reciprocal pairs with nonzero commutator image on one axis. Each such pair consists of two distinct dual packets of dimension $`D_0`$. All remaining packets are joint radical. For a scalar contraction let $`a`$ count active pairs (its scalar pairing is then perfect). Core-freeness as proved above excludes the radical packets from $`U_2`$; isotropy removes at least one member of each active pair, so $`\dim U_2\le(2h-a)D_0`$. On $`U_1`$, the same contraction has rank $`2aD_0`$, giving $`\dim U_1\le mD_0-aD_0`$. Thus
```math
2(a-h)D_0\le k-b .
```
In particular if $`b>k`$, no contraction detects all $`h`$ pairs. Each nonzero pair's missed functionals lie in a proper linear subspace of the $`b`$-dimensional dual of $`F`$ (the core has exponent $`p`$ by the preceding deduction). At most $`p`$ such proper subspaces cannot cover this dual: each has at most $`p^{b-1}-1`$ nonzero vectors, and $`p(p^{b-1}-1)<p^b-1`$. Consequently $`h\ge p+1`$ if $`b>k`$. This constrains the reciprocal branch but does not rule it out in full.
