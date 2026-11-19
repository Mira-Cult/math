# A connected Boolean family with arbitrarily many genuine triple factors

**Mira Cult · 16 November 2026**

This construction gives an infinite Boolean family with positive spectral laws
of treewidth two, genuine triple factors, and an unbounded number of feedback
vertices. It illustrates the broader coordinate-defined class covered by the
[bounded-treewidth theorem](bounded-treewidth.md). The family has other FEI
proofs; neither its construction method nor its first entropy bound is claimed
as new.

[Overview](README.md) · [Catalogue](CATALOGUE.md) · [Verification](VERIFICATION.md)

## The base Boolean function

On four spectral core coordinates put

```math
v(a,b,c,d)=3-2a-2b-c+ab+bc+cd.
```

In little-endian mask order, its values are

```math
(3,1,1,0,2,0,1,0,3,1,1,0,3,1,2,1),
\qquad \sum_s4^{v(s)}=256.
```

Set $`d_s=4-v(s)`$. To define the twelve-variable Boolean function
$`F(x,z)`$, with four core physical bits $`x`$ and eight address bits
$`z`$, use a complete four-ary prefix code with lengths $`d_s`$, ordered
by $`(d_s,s)`$. It is completely explicit as follows. Interpret $`z`$ as
an integer in $`0,\ldots,255`$; allocate consecutive aligned intervals
of lengths $`4^{4-d_s}`$ in that order. Let $`s(z)`$ be the label of the
interval containing $`z`$, and let $`q(z)=8-2d_{s(z)}`$. Define

```math
F(x,z)=(-1)^{s(z)\cdot x+
 \sum_{j=0,2,\ldots,q(z)-2}z_jz_{j+1}}.
```

The intervals are the prefix cylinders, and their low-order free bits
carry the standard bent phase. Direct Walsh inversion, or the existing
prefix-completion proof, gives

```math
\widehat F(s,t)^2=4^{v(s)-4}2^{-8}>0.
```

This is the canonical base construction in
[spectral forest arithmetic](forest-arithmetic.md), Sections 6--7,
with exact checker [check_spectral_forest_arithmetic.py](code/check_spectral_forest_arithmetic.py).
The completion proof credits the generalized Maiorana–McFarland
construction and Carlet's Fourier fiber formula; see [References](REFERENCES.md).

## Shear of independent copies

Take $`m\ge1`$ copies of $`F`$, with core coordinates
$`(a_i,b_i,c_i,d_i)`$, and disjoint eight-bit address blocks $`z_i`$.
All coordinates in the next display are physical 0/1 coordinates. Put
$`b_0=0`$ and define

**Equation (1).**

```math
G_m(x)=\prod_{i=1}^{m}
 F(a_i\mathbin\oplus b_{i-1},b_i,c_i,d_i,z_i).
```

The linear physical change in (1) is invertible: all $`b_i`$ are unchanged,
and the inverse uses the same xor operations. Hence $`G_m`$ is Boolean
on exactly $`12m`$ bits. In its spectrum, the corresponding inverse-transpose
change is

```math
\text{old }b_i=\text{new }b_i\oplus\text{new }a_{i+1}\quad(i\lt m),
```

with all other spectral coordinates unchanged, including $`b_m`$.
Consequently, putting $`t_i=a_{i+1}`$ for $`i<m`$ and $`t_m=0`$,

**Equation (2).**

```math
p_{G_m}(s,t)=2^{-8m}4^{V_m(s)-4m},\qquad
V_m(s)=\sum_{i=1}^m v(a_i,b_i\oplus t_i,c_i,d_i).
```

This proves full support and Boolean realizability, not just normalization
of a proposed Gibbs law.

## Genuine triples and graph width

For $`i<m`$, the expanded summand in (2) is

**Equation (3).**

```math
\begin{aligned}
v(a_i,b_i\oplus a_{i+1},c_i,d_i)
={}&3-2a_i-2b_i-2a_{i+1}-c_i
  +4b_i a_{i+1}\\
 &+a_i b_i+a_i a_{i+1}-2a_i b_i a_{i+1}\\
 &+b_i c_i+a_{i+1}c_i-2b_i c_i a_{i+1}+c_i d_i.
\end{aligned}
```

Both triple coefficients are $`-2`$; no other summand contains either
triple, so they cannot cancel. The logarithm of the positive law is
$`2V_m`$ plus a constant. Thus every $`m\ge2`$ has a nonzero three-way
interaction and admits no factorization into unary/pairwise potentials
on any graph in these coordinates.

For each $`i<m`$ use bags

```math
A_i=\{a_i,b_i,a_{i+1}\},\qquad
B_i=\{b_i,c_i,a_{i+1}\},\qquad
D_i=\{c_i,d_i\}.
```

Join $`A_i`$ to $`B_i`$, $`B_i`$ to $`D_i`$, and $`B_i`$ to
$`A_{i+1}`$. For the final block replace $`A_m,B_m`$ by the path bags
$`\{a_m,b_m\},\{b_m,c_m\},\{c_m,d_m\}`$, attaching the first to
$`B_{m-1}`$ when $`m\ge2`$; for $`m=1`$ there is only the final path. Each address bit is an independent singleton bag, attached
arbitrarily. These bags form a tree; all factors in (3) lie in bags; and
every variable's bags are connected. Hence the spectral law has treewidth
at most two. Its interaction graph on the nonfair core is connected.

Each $`i<m`$ has two genuine triangles sharing the edge
$`\{b_i,a_{i+1}\}`$. For $`m\ge2`$ the graph is therefore not a cactus. The triangles

```math
T_i=\{b_i,c_i,a_{i+1}\},\qquad1\le i\lt m,
```

are pairwise vertex-disjoint, so every feedback vertex set has at least
$`m-1`$ vertices. Deleting $`b_1,\ldots,b_{m-1}`$ leaves the chain
$`a_1-\cdots-a_m`$, the branches $`a_{i+1}-c_i-d_i`$, and the final
path $`a_m-b_m-c_m-d_m`$. Thus the feedback vertex number is exactly
$`m-1`$. For $`m\ge3`$, this also excludes the previous one-vertex
feedback class. Isolated address bits do not affect these conclusions.

## Exact entropy and influence

The base core marginals are

```math
P(a=1)=\frac5{64},\quad P(b=1)=\frac{35}{256},\quad
P(c=1)=\frac{55}{128},\quad P(d=1)=\frac{161}{256}.
```

The shear preserves entropy. For $`i<m`$, the new $`b_i`$ is the xor of
old $`b_i`$ and independent old $`a_{i+1}`$, so

```math
P(\text{new }b_i=1)=\frac{1585}{8192}
 =\frac{35}{256}+\frac{465}{8192}.
```

Let $`\widetilde G_m=G_m\prod_i(-1)^{x_{d_i}}`$, which complements the
spectral $`d_i`$ bits. This preserves full support, the genuine triples,
and the graph-width conclusions. Then

**Equation (4).**

```math
H(\widetilde G_m)=\frac{345m}{32},\qquad
I(\widetilde G_m)=\frac{321m}{64}+\frac{465(m-1)}{8192}.
```

These functions already satisfy constant four by (4). The construction is
used to show strictness of the *coordinate-defined spectral class*, not
to claim a first FEI result for this particular family or a new construction
method.

## Reproducibility

[check_connected_triangle_spectral_family.py](code/check_connected_triangle_spectral_family.py) implements
this recipe using standard-library exact arithmetic, verifies all 4,096
base Boolean truth values and Walsh coefficients, and verifies the full
core laws and statistics for $`m=1,2,3,4`$. The optional `--full-two-block`
check uses NumPy to build all $`2^{24}`$ truth values of $`G_2`$, compute
the integer Walsh transform, and compare every signed Fourier coefficient
against the exact inverse-transpose permutation of the product spectrum.
The analytic proof above applies to all $`m`$.
