# Fixed-gap operator transfer: a conditional interface theorem

**Mira Cult**

This note proves the coordinate and projection steps for transferring the
marked determinant method to a prescribed fixed gap. It includes the full
inverse-branch identity for the comparison kernel, the exact primitive
position projection at every intermediate step, and the parallelogram and
major-arc parameter checks.

The final transfer is conditional on the explicitly listed analytic
edge, memory, character and sparse-energy estimates of Lü–Wang–Wu,
[arXiv:2610.20242v1](https://arxiv.org/html/2610.20242v1), Sections 4–5.
Those substantive external proofs are not independently certified here.
The local inputs are the proved [root counts](root-counting-moduli.md),
the [fixed-gap conjugacy](signed-endpoint-transfer.md#5-a-fixed-gap-coordinate-change),
and [cofactor transfer](cofactor-dispersion.md).
No unmarked signed cancellation or endpoint primality follows from the
conditional marked estimate alone.

Throughout, $`g\ge2`$ is fixed, $`g`$ is even in the prime-gap application,
and all source parameters have their original meanings. In particular
$`L=\log x`$, $`J=\lfloor L^{0.01}\rfloor`$,
$`R=\lceil L^{1/2}/2\rceil`$, and the source sifting threshold is
$`Z=\exp(L^{0.24})`$. Write $`D_{\rm aux}`$ for the shared-list product
called $`D`$ in the source, to distinguish it from the endpoint
divisor cutoff. The unshared products are $`A,B\asymp Y`$.
For sufficiently large $`x`$, all auxiliary primes and sifted variables
are units modulo the fixed integer $`g`$.

## 1. The full major-arc preimage is essential

Let $`\mathfrak M_1`$ and $`\psi_1`$ be exactly the unit-shift major arcs
and smooth cutoff of source (4.9). Define

```math
\mathfrak M_{-g}=\{\theta\in\mathbb T:-g\theta\in\mathfrak M_1\},
\qquad \psi_{-g}(u)=\psi_1(-u/g),
```

and, for integer $`t`$,

```math
H_{-g}(t;A,B)=\psi_{-g}(t/Y)
 \int_{\mathfrak M_{-g}}
 e\bigl(\theta(t+gB-gA)\bigr)\,d\theta.
\qquad\text{(FG1)}
```

### Lemma FG1: exact comparison-kernel decomposition

The full preimage satisfies

```math
H_{-g}(t;A,B)
=\mathbf1_{g\mid t}\,
 \psi_1\!\left(\frac{-t/g}{Y}\right)
 \int_{\mathfrak M_1}
 e\bigl(\phi(-t/g-B+A)\bigr)\,d\phi.
\qquad\text{(FG2)}
```

In particular the comparison kernel is zero when $`g\nmid t`$.

**Proof.** For each $`\phi\in\mathfrak M_1`$, the $`g`$ inverse branches
of $`-g\theta=\phi`$ have Jacobian $`1/g`$. Their phases sum to zero
unless $`g`$ divides $`t+gB-gA`$, by the finite geometric sum.
If $`g\mid t`$, the sum of the branch Jacobians is one and their
common phase is the integrand in (FG2). The cutoff transforms as
stated. $`\square`$

Using just one inverse branch would invalidate this identity.
The support restriction cannot be checked only for the raw determinant
equation and then assumed for its comparison term.

Let $`P=(u,v)`$ and $`Q=(u',v')`$ have both coordinates coprime to $`g`$,
and let $`D_{\rm aux}`$ divide both first coordinates and be coprime
to $`g`$. Then

```math
g\mid t:=\det(P,Q)/D_{\rm aux}
\quad\Longleftrightarrow\quad
v/u=v'/u'\pmod g.
\qquad\text{(FG3)}
```

The raw equation $`t=-g(B-A)`$ and its comparison (FG1) therefore
split into the same components indexed by
$`r_0\in(\mathbb Z/g\mathbb Z)^\times`$. The entire signed operator,
including the major-arc subtraction, is block diagonal in these
components. No cross-component term has been discarded.

## 2. Conjugacy on a component and every relative position

On the component $`v\equiv r_0u\pmod g`$, use

```math
T_{g,r_0}(u,v)=\left(u,\frac{r_0u-v}{g}\right),
\qquad
\Omega'_{g,r_0}=T_{g,r_0}\Omega,
\qquad\text{(FG4)}
```

where the source rectangle is
$`\Omega=[d_0YM,16d_0YM]\times[N,2N]`$.
The inverse is $`(x,y)\mapsto(x,r_0x-gy)`$.
This maps primitive positions in that component bijectively onto
primitive positions in $`\Omega'_{g,r_0}`$ whose first coordinate
is a unit modulo $`g`$. It leaves the first coordinate and the prime
lists unchanged, hence preserves the state measure and list
symmetrization. Its determinant is $`-1/g`$.

Thus $`t'=\det(TP,TQ)/D_{\rm aux}=-t/g`$ and the raw condition becomes
$`t'=B-A`$. Lemma FG1 transforms the comparison to the same unit-shift
kernel, without an extra factor $`g`$ or $`1/g`$.

Choose the normalized completion and the diagonal matrix

```math
G=\begin{pmatrix}u&c\\v&d\end{pmatrix}\in{\rm SL}_2(\mathbb Z),
\qquad 0\le c\lt u,\qquad E_g=\begin{pmatrix}1&0\\0&-g\end{pmatrix}.
```

The transformed completion is

```math
G'=T_{g,r_0}GE_g
=\begin{pmatrix}
u&-gc\\
(r_0u-v)/g&d-r_0c
\end{pmatrix}
\in{\rm SL}_2(\mathbb Z).
\qquad\text{(FG5)}
```

For a primitive relative vector $`z`$, its original position is
$`GE_gz`$. Consequently

```math
\gcd((GE_gz)_1,(GE_gz)_2)=\gcd(z_1,gz_2)=1
\quad\Longleftrightarrow\quad (z_1,g)=1.
\qquad\text{(FG6)}
```

Also $`(GE_gz)_1\equiv uz_1\pmod g`$, so (FG6) is exactly the
unit-first-coordinate restriction. The second coordinate then has
the same unit ratio $`r_0`$. This applies to every intermediate
position, not only to the initial and final endpoints.

Write $`\theta_0=c/u`$ and put

```math
\tau_g(z)=z_1-g\theta_0z_2.
```

Direct multiplication gives

```math
(G'z)_1=u\tau_g(z),\qquad
r_0(G'z)_1-g(G'z)_2
=v\tau_g(z)-\frac{gz_2}{u}.
\qquad\text{(FG7)}
```

The original root coordinate transforms as
$`r_{TP}=-g\,r_P\pmod1`$.
For any primitive $`z`$ and complement $`w`$ with $`\det(z,w)=1`$,

```math
r_{G'z}=\frac{\tau_g(w)}{\tau_g(z)}\pmod1,\qquad
\frac{\partial}{\partial\theta_0}
\frac{\tau_g(w)}{\tau_g(z)}
=-\frac{g}{\tau_g(z)^2}.
\qquad\text{(FG8)}
```

The good-state tests must use these transformed ratios, just as
source (4.19) uses $`-2r_P`$. Multiplication by $`-g`$ preserves Haar
measure on the circle, so the source's exceptional-ratio measure
bound is unchanged.

## 3. Root replacement and the parallelogram budget

For each fixed ratio component, RC2 supplies the root measure

```math
\frac{1}{\zeta(2)\,g\prod_{p\mid g}(1+1/p)}
\,d(u/(d_0YM))\,d(v/N)\,d\theta_0,
\qquad\text{(FG9)}
```

and independent auxiliary lines with probability $`1/(p+1)`$.
The total mass after summing the $`\varphi(g)`$ components is bounded;
the component factor is an exact density, not an adjustable constant.

The source retains the original rectangle when averaging roots.
Its transformed parallelogram is retained through the exact projection

```math
\chi_g(z)=
\mathbf1_{G'z\in\Omega'_{g,r_0}}\,
\mathbf1_{(z_1,g)=1}.
\qquad\text{(FG10)}
```

There is no need to enlarge $`\Omega'_{g,r_0}`$ to an axis-parallel
rectangle. Such an enlargement can cost an unbounded aspect-ratio
factor even for $`g=2`$, which source Section 4.3 explicitly avoids.

The path and boundary accounting extends as follows. Unit-shift
kernel support gives $`|\det(z,z')|\ll d_0Y`$.
Using $`\tau_g(z),\tau_g(z')\in[1/16,16]`$, the identity

```math
\frac{z'_2}{\tau_g(z')}-\frac{z_2}{\tau_g(z)}
=\frac{\det(z,z')}{\tau_g(z)\tau_g(z')}
```

shows $`|z_j|\ll_g Rd_0Y`$ along a path of length at most $`2R`$.
Writing $`s=u/(d_0YM)`$ and $`t_0=v/N`$, the boundaries of (FG10) are

```math
s\tau_g(z)\in\{1,16\},\qquad
t_0\tau_g(z)-\frac{gz_2}{d_0YMN\,s}\in\{1,2\}.
\qquad\text{(FG11)}
```

The respective derivatives in $`s`$ and $`t_0`$ are $`\tau_g(z)`$,
bounded away from zero. Other derivatives are $`\exp(o(L))`$ for
fixed $`g`$. Equation (FG8) gives the same monotonicity for good-state
boundaries. In particular
$`|gz_2|/(d_0YMN)\ll_g R/(MN)`$; no factor $`d_0YM/N`$ appears.

Source (4.30)--(4.32) use these facts to approximate the position
and good-state indicators by root-coordinate cubes. Its retained
auxiliary moduli satisfy
$`\log S\ll_K L^{0.96}`$, and it permits
$`S\le\exp(O_K(L^{0.98}))`$.
RC2 at the required modulus $`gS`$ has normalized error

```math
O_g\!\left(\exp(O_K(L^{0.98}))x^{-\delta/32}\right)
=x^{-\delta/32+o(1)}
\qquad\text{(FG12)}
```

when $`M,N\ge x^\delta`$.
For example choose $`c_\delta=\delta/64`$ in the source cube argument.
Its $`x^{o(1)}`$ term counts and $`O(x^{3c_\delta/8})`$ cubes are then
absorbed. The resulting power saving is smaller than
$`L^{-2AR}`$ for every fixed $`A`$, since $`R\asymp L^{1/2}`$.
The Bonferroni truncation error in the source remains
$`\exp(-cL^{0.76}\log L+O_K(L^{0.73}))`$.
Thus the displayed exponent $`1/32`$ in RC1 pays root replacement.

The fixed congruence test $`(z_1,g)=1`$ is independent of the real root
variables, so it contributes no new boundary surfaces.
The new constants are allowed to depend on $`g`$.
These observations give no uniform growing-$`g`$ theorem.

## 4. Why the projection is harmless inside the moment

This is the decisive operator check. Source (4.34) already defines

```math
P_\chi F(z,\boldsymbol p,\mathfrak m)=
\mathbf1_{G'z\in\Omega'}\mathbf1_{z_1\ {\rm odd}}
F(z,\boldsymbol p,\mathfrak m).
```

Replace its position multiplier by (FG10).
It still has norm at most one and depends on neither active-list
ordering, auxiliary projective-line variables being averaged, nor
memory coordinates.

### Lemma FG2: stability under a position-only projection

At fixed real root parameters, work within the source's existing finite
ambient position space, retaining its positive $`\tau`$ range and
good-state restrictions. Replace the geometric position projection by
any indicator $`\chi(z)`$ independent of the active prime lists,
the auxiliary projective-line variables being averaged, and the memory
variables. The following operator statements are preserved. Root
averaging of a root-dependent indicator requires a separate boundary
argument, supplied for (FG10) in Section 3.

1. $`G_j`$ commutes with $`P_\chi`$, because it fixes $`z`$.
   List permutations and memory-coordinate symmetrizations commute
   with it as well.
2. The clean-edge signed estimate is stable under the projection.
   After the source's lattice coordinate change
   $`z=\mathcal B_D\mathbf k`$, equation (4.45) writes the actual
   operator as
   $`\iota_s^*D_s\mathcal E_0D_t\iota_t`$.
   The factors $`\chi(\mathcal B_D\mathbf k)`$ and
   $`\chi(\mathcal B_D\boldsymbol\ell)`$ are bounded endpoint
   multipliers in $`D_s,D_t`$. Therefore the bound for
   $`\|\mathcal E_0\|`$ is unchanged.
3. The dirty-edge estimates in (4.48)--(4.50) are absolute row/column
   bounds. Removing allowed positions can only decrease these
   bounds. In particular the extra condition $`(z_1,g)=1`$ does not
   affect the unique-residue argument at an auxiliary prime.
4. Memory-truncation and high-rank coincidence errors are bounded
   by absolute path sums and decrease upon inserting $`\chi`$.
   In the low-rank expansion (4.61)--(4.62), the inserted choice
   phases concern prime-list or memory coordinates. They commute
   with $`P_\chi`$, so each modified-edge bound in (4.41) remains
   valid.

**Proof.** The first statement is immediate from the defining
operations. The second is precisely a compression by bounded
multipliers; the source's ambient signed determinant matrix contains
no parity restriction. The third follows from the positive weighted
Schur sums. For the fourth, retain $`\prod_j\chi(z_j)`$ in every path
before doing the local prime-line averages. It is independent of
those lines, so the identity (4.37) and the $`G_j,E_j`$ reconstruction
are unchanged. Bound each resulting chain using the individual
compressed operators. This proves all assertions. $`\square`$

This proof does not use the generally invalid assertion that every
diagonal entry of a high power decreases under arbitrary compression.
It checks the source's auxiliary operator chain and the terms used
to impose distinct prime selections.

There is no hidden dependence on $`g`$ in the clean determinant
matrix itself. Source (4.40)--(4.44) use only a positive linear
functional $`\tau`$ with $`\tau(z')/\tau(z)\in[1/16,16]`$ and the
good-state Diophantine test at a chosen $`z_*`$. The same argument with
$`\tau_g`$ gives a shared-prime lattice of determinant $`D_{\rm aux}`$
and a box with side lengths
$`A'B'\asymp Y`$, $`Y^{0.1}\le A',B'\le Y^{0.9}`$.
The tensor-product exponential matrix in (4.45)--(4.46) is identical.

For dirty raw edges, source (4.47) gives
$`j_1=P_{\rm full}-D_{\rm aux}p_*ZT_f`$.
The line condition at $`p_*`$ fixes one residue of the scalar $`h`$
in $`z'=j_1w_z+hz`$. Goodness separates the possible phases
$`D_{\rm aux}ZT_f\,\tau_g(w_z)/\tau_g(z)`$.
Additional deletion by (FG10) cannot create more solutions.
The dirty comparison count (4.49) is likewise an upper bound on
an unrestricted lattice box. All auxiliary primes are coprime to
the fixed $`g`$ once $`x`$ is large.

It follows that, **relative to the analytic edge and distinctness
contracts proved in the source**, the moment bound (4.52) holds
componentwise with (FG9) in place of the odd-coordinate density.
The error accounting in Section 3 then gives its arithmetic version.
The present audit checks the transformation and stability of these
contracts; it does not certify every analytic estimate underlying them.

## 5. From moments to endpoint pairings

Source Section 4.6 does not require endpoint coefficients to factor
in the transformed coordinates. On a ratio component the old
coefficient becomes

```math
f'_{r_0}(x,y)=
\overline{\alpha_{x/G_0(x)}}\,\beta_{r_0x-gy},
\qquad\text{(FG13)}
```

where $`G_0(x)`$ extracts the auxiliary-prime part of the first
coordinate. Supremum and $`\ell^2`$ norms are unchanged by the
unitary position map.

The source's automatic primitivity argument also extends.
Sifting makes every common divisor of $`D_{\rm aux}Bm`$ and $`s`$
exceed $`Z`$, while such a divisor divides the nonzero determinant
$`t`$, whose cutoff gives $`0\lt |t|\ll_g Y=o(Z)`$.
Nonzeroness follows from $`(A,B)=1`$ and the auxiliary-free long
variables, exactly as in source Section 4.6.
No terms are lost by restricting to primitive positions.

The slope difference in the original coordinates is now
$`O_g((d_0YM^2)^{-1})`$.
The partition used in (4.64)--(4.67) therefore has $`O_g(1)`$
neighboring intervals and $`O_g(d_0Y)`$ positions per interval.
These are fixed constants. The source's resulting factor
$`(d_0Y)^{1/(2R)}`$ is still bounded because
$`\log(d_0Y)=O_K(L^{0.21})`$.

A fixed covering congruence on a long product can be expanded in
Dirichlet characters. Each character factor attaches to one of the
two endpoint vectors, possibly giving different source and target
vectors. Source (4.67)--(4.68) explicitly permits such pairings.
The expansion's total absolute coefficient mass is one.
Likewise the phase $`G_0(P_1)^{it}`$ inserts $`(A/B)^{it}`$ and changes
neither endpoint norm nor list-permutation invariance.
Thus the source's minor-arc argument remains phase uniform at
this interface. It does not require differentiating the phase.

## 6. Fixed-gap major-arc normalization

The source's Section 5.2 can be tested separately from the preceding
minor-arc argument. The full preimage $`\mathfrak M_{-g}`$ has rational
centers of denominator at most $`gL^{A_0}`$, at most
$`O_g(L^{2A_0})`$ arcs, and branch widths
$`O(L^{A_0}/(gY))`$. The looser bound
$`O_g(L^{A_0}/Y)`$ is sufficient for the source normalization.

On each arc $`\theta=h/k+\lambda/Y`$, the exact six-variable phase is

```math
e\!\left(\frac{h(Bmn-Ars+gB-gA)}{k}\right).
\qquad\text{(FG14)}
```

All variables are units modulo $`k`$ for sufficiently large $`x`$.
It therefore has the same character expansion, with total absolute
coefficient mass at most $`k^6`$.
A fixed covering modulus $`Q`$ changes the character modulus to
at most $`\operatorname{lcm}(k,Q)\le Qk`$.
This is still a fixed power of $`\log x`$ when $`Q`$ is fixed, or
bounded by a specified fixed power of $`\log x`$.

The separated auxiliary polynomial is now

```math
B_{g,\lambda}(t)=
\frac{\prod_iV_i^{-1}}{Y}
\sum_B\eta(B/Y)e(g\lambda B/Y)\chi_B(B)B^{it}.
\qquad\text{(FG15)}
```

The smooth function replacing source $`g_\lambda(y)`$ is
$`y\eta(y)e(g\lambda y)`$.
For fixed $`g`$, its Mellin-transform norm and the derivatives of the
near-diagonal kernel retain the source's fixed logarithmic bounds,
with constants depending on $`g`$.
The support in the source's variable
$`\zeta=X\log(w/w')`$ is $`O_g(1)`$.
The exact scale calculation is unchanged:

```math
(YMN)^2\,X^{-1}\,Y^{-1}\asymp XY.
\qquad\text{(FG16)}
```

Auxiliary-product Mellin phases shift only the frequency in
$`B_{g,\lambda}`$. Source Lemma 5.2 and (5.15)--(5.16) state
uniformity in that arbitrary real shift.
The long Möbius coefficient still requires Proposition 2.2,
and the sparse-frequency energy estimate still requires Lemmas
5.1--5.2. These are distinct analytic inputs; the root-counting
theorem supplies none of them.

Accordingly the fixed-$`g`$, fixed-$`Q`$ major-arc extension has no
additional denominator or normalization obstacle at these checked
interfaces. This statement is conditional on the validity of the
underlying source estimates. It makes no claim about growing
power-size moduli $`Q`$, where the character--Mellin input needs
new uniformity and exceptional-character treatment.

## 7. Precise conditional transfer and remaining scope

The checked extension can be stated as the following contract.

For each requested saving exponent $`A`$, choose the source parameters
$`K`$ and $`A_0`$ sufficiently large, in the order and ranges required
by the cited source estimates, and then hold them fixed as
$`x\to\infty`$. These choices may depend on $`A`$ and the other fixed
data. The marked family and major-arc set in (FG17) use these choices;
the constants and large-$`x`$ threshold may depend on them. No assertion
of every logarithmic saving for one previously fixed marked family
and major-arc set is intended.

Assume the source's unit-shift clean and dirty edge estimates
(4.41), (4.46), (4.48)--(4.51), its memory/distinctness reconstruction
(4.53)--(4.62), and its endpoint and one-edge estimates are valid.
Use RC1--RC2 for root counting. Then the same marked Type II
minor-arc estimate holds for every fixed $`g`$ and fixed covering
data, with constants depending on those fixed data, and uniformly
under the auxiliary-product Mellin phases:

```math
Q_{g,Q,Y}-Q_{g,Q,Y}^{\rm maj}
\ll_{g,Q,\delta,C,A}XYL^{-A}.
\qquad\text{(FG17)}
```

Adding the source's character--Mellin and sparse-energy contracts
from Sections 2.2 and 5 yields the corresponding marked base
energy estimate. This is an implication from explicit proof
interfaces, not an inference from the numerical statement of a
bounded-gap or one-prime theorem.

| Issue | What is discharged here | What remains |
|---|---|---|
| Ratio components | Exact vanishing of both raw and comparison kernels outside $`g\mid t`$ | No extra fixed-$`g`$ component estimate |
| Primitive intermediate positions | Exact projection $`(z_1,g)=1`$, retained inside every auxiliary chain | Independent verification of the underlying source chains |
| Parallelogram support | Exact original-coordinate averaging and boundary budget | No bounding-box aspect-ratio assumption |
| Root density | RC2 gives the exact component factor and a sufficient power-saving error | No uniform growing-$`g`$ claim |
| Minor-arc operator | Position projections preserve the actual clean, dirty and coincidence interfaces | Complete source-proof audit is not performed |
| Major arcs and phase family | Fixed-$`g`$ arc counts, character moduli, Mellin scale and auxiliary phase are compatible | Source Propositions 2.2, 5.3 and Lemmas 5.1--5.2 remain substantive inputs |
| Endpoint remainder | None of these steps removes the marking | Signed rough-sector transfer remains open |

In particular, this audit does not weaken the unsigned obstruction in
[rough-endpoint-marking.md](rough-endpoint-marking.md),
Theorem 6. Even if the marked base estimate is independently certified,
the actual signed endpoint remainder still needs a mechanism retaining
its omitted sector.

