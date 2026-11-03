# Fixed-field prime inputs in arbitrary cyclotomic degree

Author: /root/analytic. New manuscript-local results; no permanent claim IDs.
This source extends the analytic and representative-geometry interfaces. It
does not modify or retrospectively enlarge the frozen quartic manuscripts.
The physical array theorem, arithmetic classification of allowable orders,
and exact normalization algorithm are separate dependencies.
Status: conventional author proofs with the stated dependencies; independent
review is recorded separately at an exact source revision.

For new fields the model is the **minimum Minkowski energy** representative
with a symmetric first torsion sector and exact coefficient ties. This is a
different model from a general logarithmic parallelotope. The existing
quartic balanced-log pools retain their original definitions. The conclusions
below apply to both models when their stated geometric hypotheses hold.
The canonical continuation definitions, including conductor reduction, are
in [PROBLEM.md](../PROBLEM.md#fixed-conductor-continuation-2026-11-03).
The rational field is outside this totally complex argument and has the
separate pool obstruction and repair stated there.

## 1. Fixed data and exact analytic sources

Fix a cyclotomic field $`K=\mathbb Q(\zeta_m)`$, $`m>2`$, of degree
$`r=2s`$. Fix an ordered integral basis and one embedding from each complex
conjugate pair,


```math
\sigma:K\longrightarrow\mathbb C^s\cong\mathbb R^r.
```


Write $`h=h_K`$, $`w=|\mu(K)|`$, and $`\mathcal R=\mathcal R_K`$ for its
class number, number of roots of unity, and standard regulator. For $`s=1`$
the regulator is one. All implied constants and thresholds may depend on
this fixed field, the chosen basis and embeddings, and the fixed exponents
or shape bounds specified in a lemma. No uniformity in $`m,r,h,\mathcal R`$
or a varying family of unit domains is asserted.

The analytic sources are the same versions audited for the quartic argument:

- **KM:** Wataru Kai, *Notes on Mitsui's Prime Number Theorem with Siegel
  zeros*, [arXiv:2209.11816v3](https://arxiv.org/html/2209.11816v3),
  Theorem 3.1.1 and Appendices A.5--A.6.
- **KL:** Wataru Kai, *Linear patterns of prime elements in number fields*,
  [arXiv:2306.16983v5](https://arxiv.org/html/2306.16983v5),
  Theorem 6.1, Theorem 12.1 and Remarks 12.2--12.4.

KM counts prime elements in any fixed number field, with the class-number
factor present. KL permits a fixed integral basis for the target ideal
$`O_K`$, and gives arbitrary fixed powers of logarithmic saving for convex
domains. Its required pairwise finite-cokernel condition is checked below.
Neither result requires class number one.

Use ordinary Lebesgue measure on $`\mathbb C^s`$. The lattice covolume is
$`2^{-s}\sqrt{|D_K|}`$; coefficient and Minkowski norms are equivalent by
fixed constants. Define $`N(z)=\prod_{j=1}^s|z_j|^2`$. A prime element is an
element whose principal ideal is a nonzero prime ideal. An irreducible with
nonprime principal ideal is never an entry or target.

## 2. A geometric interface, and the energy model

Let


```math
H=\{x\in\mathbb R^s:\ \sum_jx_j=0\},\qquad
 \Lambda=\{(\log|\sigma_j(u)|)_{j=1}^s:\ u\in O_K^\times\}.
```


Dirichlet's unit theorem makes $`\Lambda`$ a full lattice in $`H`$, and its
kernel is precisely the full torsion group. This is the full unit lattice;
no subgroup of convenient units is silently substituted for it.

**Geometric hypothesis G.** Away from a boundary of measure zero, the
canonical representative domain has the form


```math
\mathcal D_F=\left\{z_j=\rho e^{x_j}e^{i\theta_j}:
  \rho\gt 0,\ x\in F,\ -\pi/w\lt \theta_1\lt \pi/w,\
  \theta_2,\ldots,\theta_s\in\mathbb R/2\pi\mathbb Z\right\},       \qquad\text{(2.1)}
```


where $`F\subset H`$ is a bounded full-unit fundamental cell of positive
measure, its closure is the closure of its interior, and its boundary has
measure zero. Boundary conventions choose exactly one associate. The
strict interior of (2.1) consists of canonical representatives, with
multiplicity one. Put $`\mathcal D_{F,1}=\mathcal D_F\cap\{N(z)\le1\}`$.

For $`s=1`$, interpret $`H=F=\{0\}`$, zero-dimensional volume as one, and
interior in the relative topology of $`H`$.

A centered logarithmic parallelotope satisfies G as a geometric domain.
That observation alone does **not** supply an effective exact boundary
algorithm in unit rank at least two: its face comparisons involve the
inverse matrix of unit logarithms. No general decision procedure for those
equalities is assumed here.

For the new energy normalization the log cell is


```math
F_E=\left\{x\in H:\ \sum_j e^{2x_j}
       \le \sum_j e^{2(x_j+\lambda_j)}
       \text{ for every }\lambda\in\Lambda\right\}.             \qquad\text{(2.2)}
```


The [normalization source, GN1--GN2](general_normalization_local.md), supplies
the exact finite-ellipsoid algorithm, the full associate comparison,
boundedness of $`F_E`$, and the fact that only finitely many unit inequalities
are relevant on bounded sets. The following observations explain why the
analytic geometry is unconditional with those elementary normalization facts.

For nonzero $`\lambda\in\Lambda`$, AM--GM gives
$`\sum_j e^{2\lambda_j}>s`$. Thus $`0`$ is a strict interior point of
(2.2): the exponential sum tends to infinity with $`\|\lambda\|`$, so
large unit vectors remain uniformly strict in a fixed neighborhood of zero;
the remaining finitely many strict inequalities give a smaller neighborhood.
Write $`y_j=e^{2x_j}`$. Its inequalities are linear homogeneous inequalities
in the positive $`y_j`$, together with $`\prod_jy_j=1`$. Interpolate $`y`$
toward $`(1,\ldots,1)`$, then rescale all coordinates by the same positive
factor to restore product one. Every nontrivial unit inequality becomes
strict. Hence every cell point is a limit of interior points.

The finitely many boundary equations are nonzero real analytic equations
on $`H`$. Equivalently they are nonzero linear equations in positive $`y`$
restricted to the product-one surface. They have measure zero. Minimal
energy chooses a fundamental cell up to these boundaries, since every
unit orbit has a minimizer, and two distinct minimizers give an equality
in one of (2.2). Torsion does not change energy, and the first sector
removes its multiplicity. Other exact tie rules only affect the null
boundary. Thus the energy domain satisfies G.

This argument does not require the cell to be convex in logarithms, and
does not assert that its centroid belongs to its support.

## 3. Uniform prime boxes in any fixed arithmetic rank

For a convex open set $`C`$ in an enclosing Minkowski box of radius
$`C_0Y`$, a nonzero integral ideal $`\mathfrak q`$, and a unit residue
$`a\bmod\mathfrak q`$, KM gives


```math
\sum_{\substack{\pi\in C\cap O_K,\ (\pi)\ {\rm prime}\\
                         \pi\equiv a\ (\mathfrak q)}}\log N(\pi)
 =\frac{\kappa_K}{\varphi_K(\mathfrak q)}
       \int_C\{1-\chi(z;a)N(z)^{\beta-1}\}\,dz
   +O_K(Y^r e^{-c_K\sqrt{\log Y}}),                            \qquad\text{(3.1)}
```


where $`\kappa_K=w/(\pi^s h\mathcal R)`$. The secondary term is omitted
only when the exceptional character does not exist. The allowed norm of
$`\mathfrak q`$ is at least $`\exp(c'_K\sqrt{\log Y})`$. The error is
measured against the enclosing radius, not the volume of $`C`$.

**Lemma GW (prime boxes).** Fix $`A,B,C_0>0`$. Let
$`H_Y=Y/(\log Y)^A`$. Every coefficient box whose sides are comparable to
$`H_Y`$, contained in a coefficient box of radius $`C_0Y`$, contains


```math
\gg_{K,A,B,C_0}
       \frac{H_Y^r}{\varphi_K(\mathfrak q)\log Y}               \qquad\text{(3.2)}
```


prime elements in each unit class modulo each ideal satisfying
$`N\mathfrak q\le(\log Y)^B`$, for all sufficiently large $`Y`$.
The threshold is uniform in the center, ideal, and residue, and is
ineffective. The same holds for fixed-shape parallelepipeds.

**Proof.** For each complex embedding the subset of a unit coefficient
box on which that embedding has modulus less than $`\delta`$ has volume
$`O_K(\delta^2)`$, uniformly under translations. Remove these $`s`$
subsets and a thin boundary strip. For fixed small $`\delta>0`$, a point
remains, and a fixed smaller box about it avoids all the embedding zeros.
After scaling, there is a subbox of volume $`\gg H_Y^r`$ on which every
$`|\sigma_j(z)|\ge cH_Y`$, so
$`\log N(z)\ge r\log Y-O_{K,A}(\log\log Y)`$.

A real Hecke character has trivial archimedean component on
$`(\mathbb C^\times)^s`$, which is connected. Its value at fixed residue
therefore has a constant sign. KL Theorem 6.1 gives
$`1-\beta\gg_{K,\epsilon}N(\mathfrak f_\chi)^{-\epsilon}`$ for every fixed
$`\epsilon>0`$, with an ineffective constant. Choose
$`\epsilon=1/(2\max(B,1))`$. On our subbox,
$`(1-\beta)\log N(z)\gg\sqrt{\log Y}`$, uniformly in the prescribed ideals.
Eventually the integrand in (3.1) is at least $`1/2`$, regardless of sign.
The main term is at least a constant times
$`Y^r/(\log Y)^{rA+B}`$, which dominates its enclosing-radius error.
Each prime weight is $`O_K(\log Y)`$. This proves (3.2). QED.

This allows a center of the form $`(cY,0,\ldots,0)`$. There are still
$`r`$ real dimensions of volume: the other embeddings can vary on the
scale $`H_Y`$, and the logarithm of the product norm remains comparable
to $`\log Y`$. It does not justify a box of radius $`O(R)`$ about a point
of size $`nR`$, whose relative volume may be a negative power of $`n`$.

GW counts arbitrary prime elements. Only a box strictly inside the
canonical domain gives input entries automatically. Other boxes provide
target sums. A nonprincipal prime ideal is never counted as an element.

## 4. Principal-prime pool law and centroid

Use one canonical representative for every principal prime ideal other
than the explicitly omitted ramified classes; retain every residue degree.
This is a bijection between the input associate classes and those prime
ideals. Order by absolute norm and the frozen exact coefficient tie.

**Lemma GP (density, scales, and mean).** Assume G. Let $`M`$ be the
length of an initial pool, $`B_M`$ its largest norm, $`R=B_M^{1/r}`$, and
$`\overline p_M=M^{-1}\sum_{j\le M}\sigma(p_j)`$. Then


```math
M\sim \frac{\mathrm{Li}(B_M)}{h}
       \sim \frac{B_M}{h\log B_M},\quad
 B_M\sim hM\log M,\quad
 R\sim(hM\log M)^{1/r},                                    \qquad\text{(4.1)}
```


and


```math
\frac{\overline p_M}{R}\longrightarrow(c,0,\ldots,0),\qquad
 c=\frac{r}{r+1}\frac{\sin(\pi/w)}{\pi/w}
           \frac{1}{|F|}\int_F e^{x_1}\,dx.                 \qquad\text{(4.2)}
```


Here $`dx=dx_1\cdots dx_{s-1}`$, with $`x_s=-\sum_{j<s}x_j`$.

**Proof.** In the coordinates of (2.1) the Jacobian is


```math
dz=s\rho^{r-1}\,d\rho\,dx_1\cdots dx_{s-1}
                       \,d\theta_1\cdots d\theta_s.        \qquad\text{(4.3)}
```


Indeed the logarithmic radial change
$`\log|z_j|=\log\rho+x_j`$ has determinant $`s`$; the product of the
polar radial factors is $`\rho^{2s}`$. The full unit-log covolume in
these $`s-1`$ coordinates is $`\mathcal R/2^{s-1}`$, since the standard
regulator uses twice the complex logarithms. Thus


```math
|\mathcal D_{F,1}|=
  \frac{s}{r}\frac{(2\pi)^s}{w}\frac{\mathcal R}{2^{s-1}}
  =\frac{\pi^s\mathcal R}{w},\qquad
 \kappa_K|\mathcal D_{F,1}|=\frac1h.                        \qquad\text{(4.4)}
```


These equalities use the full unit cell, not a finite-index subgroup.

Approximate any fixed annular portion of $`\mathcal D_{F,1}`$ by finite
unions of boxes, using its null boundary and boundedness. Formula (3.1)
with trivial modulus gives its prime-element weighted count with leading
density $`\kappa_K`$. The part with radial coordinate below $`\delta`$
is contained in a box of radius $`O_K(\delta R)`$, so its weighted
contribution is $`O_K(\delta^rR^r)`$. First let $`R`$ grow and then
$`\delta`$ decrease. Boundary counts are bounded by outer box covers and
have zero limiting density. Canonical tie choices consequently cause no
change to the leading weighted count. We obtain
$`\sum_{N(p)\le B}\log N(p)\sim B/h`$; partial summation yields
$`\#\{p:N(p)\le B\}\sim\mathrm{Li}(B)/h`$.

On a fixed annulus, $`\log N(p)=\log B+O_\delta(1)`$, giving ordinary
volume distribution for the unweighted count as well. The part of radius
$`\delta R`$ has count $`O_K(\delta^r B/\log B)`$ and first moment
$`O_K(\delta^{r+1}RB/\log B)`$. Hence its contribution to the normalized
mean disappears. In (4.3) the radial average is $`r/(r+1)`$; the first
angular average is $`\sin(\pi/w)/(\pi/w)`$; every other angular average
is zero. This proves (4.2).

A norm tie contains at most $`r`$ prime ideals: its norm is a unique
rational prime power $`p^f`$, and at most $`r`$ prime ideals lie above
$`p`$. Cutting a tie changes at most $`r-1`$ entries, each of size $`O_K(R)`$.
The finitely many omitted ramified classes also have no leading effect.
This proves (4.1) and the assertion for every initial segment. QED.

Higher residue degrees contribute $`O_K(B^{1/2})`$ prime ideals to a
norm cutoff $`B`$, hence lower order; this bound is an asymptotic
observation, not permission to remove those entries. In particular,
principal prime ideals of higher residue degree and inert prime elements
remain in the exact pool and its exact total.

For the array use $`M=n^D`$, $`D=2`$ or $`3`$. The resulting scales are


```math
R\asymp_K n^{D/r}(\log n)^{1/r},\qquad
 Y\asymp_K nR,\qquad H_Y=Y/(\log Y)^A.                     \qquad\text{(4.5)}
```


For fixed $`r`$, every positive power of $`n`$ still dominates every
fixed power of $`\log n`$, however large the latter exponent is.

## 5. Interior chords centered at the true mean

**Lemma GE (arbitrary-rank symmetric endpoint geometry).** Assume G.
There exist $`r`$ real-linearly independent vectors $`v_1,\ldots,v_r`$,
positive constants $`\varepsilon,\delta`$, and a fixed inverse-matrix
bound, such that every point


```math
(c,0,\ldots,0)\pm v_j/2
```


has a $`\delta`$-neighborhood inside the strict canonical domain and
satisfies $`N(z)<1-\varepsilon`$. The endpoint neighborhoods may be
chosen pairwise disjoint.

**Proof.** Let
$`\gamma=(r/(r+1))\sin(\pi/w)/(\pi/w)`$, so $`0<\gamma<1`$.
Put $`A_1=\max_{\overline F}e^{x_1}`$. Formula (4.2) gives
$`0<c=\gamma\,\mathbb E_F e^{x_1}\le\gamma A_1<A_1`$.
Since the closure of $`F`$ is the closure of its interior, choose
$`x^\ast\in\mathrm{int}F`$ with $`e^{x^\ast_1}>c`$. Set
$`\rho^\ast=c e^{-x^\ast_1}<1`$, and define


```math
a=(c,\rho^\ast e^{x^\ast_2},\ldots,\rho^\ast e^{x^\ast_s}),
 \quad
 b=(c,-\rho^\ast e^{x^\ast_2},\ldots,-\rho^\ast e^{x^\ast_s}).
                                                               \qquad\text{(5.1)}
```


Both have first phase zero, the same strict log point $`x^\ast`$, and
norm $`(\rho^\ast)^r<1`$. Their midpoint is exactly $`(c,0,\ldots,0)`$.
Thus small balls about $`a,b`$ are strict interior endpoint boxes with a
fixed norm margin. Equivalently, the set of possible gap vectors $`v`$
such that the mean plus and minus $`v/2`$ are interior has a nonempty
open subset.

Any nonempty open subset of $`\mathbb R^r`$ contains $`r`$ linearly
independent vectors: successively avoid the proper subspace spanned by
previous choices. Choose them distinct also up to sign. Their fixed
matrix is invertible; shrinking neighborhoods preserves its inverse
bound and separates the finitely many endpoints. For $`s=1`$, (5.1)
has $`a=b=c`$, but $`c<1`$ lies in the interior of the sector disk.
The same open-neighborhood argument gives the required two directions.
QED.

In particular no bound $`c<1`$ is needed in higher degree, and no
convexity of the log cell is used. The maximal first amplitude of the
cell, together with radial slack, supplies the endpoints.

By GP, centers
$`\overline p_M\pm Rv_j/2`$ eventually lie in the same fixed interior
neighborhoods after division by $`R`$. Thus boxes of radius
$`\eta R`$, $`\eta=(\log R)^{-a}`$, about these **actual-mean** endpoints
stay strictly below the last norm cutoff. Only
$`\overline p_M/R\to(c,0,\ldots,0)`$ is required; a convergence rate
smaller than $`\eta`$ is unnecessary because the endpoint margin is fixed.

## 6. Arbitrary ideal moduli and exact three-prime completion

There is no need to assume that a controller modulus is principal.

**Lemma GL (principal contained modulus and compatible lifts).** Let
$`\mathfrak q`$ be a nonzero integral ideal and $`d=N\mathfrak q`$.
Then $`dO_K\subset\mathfrak q`$. Suppose every norm-two prime ideal
divides $`\mathfrak q`$, and unit classes $`b_1,b_2,b_3\bmod\mathfrak q`$
sum to $`T\bmod\mathfrak q`$. They lift to unit classes
$`a_1,a_2,a_3\bmod dO_K`$ whose sum is $`T\bmod dO_K`$.

**Proof.** The finite additive group $`O_K/\mathfrak q`$ has order $`d`$,
so $`d`$ annihilates it, proving the containment. At a prime ideal
dividing $`\mathfrak q`$, arbitrarily lift the first two classes to the
required power dividing $`dO_K`$, and set the third to their complement
in $`T`$. All three remain units because their images modulo that prime
are the prescribed nonzero images. At a prime divisor of $`dO_K`$ absent
from $`\mathfrak q`$, its residue field has size $`Q\ge3`$.
There are three nonzero residues summing to any prescribed total:
the counts for the first two residues are $`(Q-1)(Q-2)`$ for total zero
and $`Q^2-3Q+3`$ for nonzero total. Lift the first two and take the
complement for the third. CRT proves the assertion. QED.

**Lemma GT (uniform exact-total targets).** Fix $`A,B,C_0>0`$.
Let $`T\in O_K`$ with coefficient size at most $`C_0Y`$, let
$`H_Y=Y/(\log Y)^A`$, and let $`N\mathfrak q\le(\log Y)^B`$.
Assume the norm-two and three-unit-residue conditions of GL.
For every sufficiently large $`Y`$ there are prime elements $`p_j`$
in those prescribed classes such that


```math
p_1+p_2+p_3=T,\qquad
 \|p_j-T/3\|_\infty\le H_Y.                               \qquad\text{(6.1)}
```


The threshold is uniform and ineffective; the targets need not be
canonical. Every embedding of $`T/Y`$ is allowed to approach zero.

**Proof.** Apply GL and choose representatives $`a_1,a_2`$ modulo
$`dO_K`$ with coefficients of size $`O_K(d)`$, where
$`1\le d\le(\log Y)^B`$. Use the three $`O_K`$-linear forms on
two free $`O_K`$ variables


```math
\psi_1=a_1+dx,\quad \psi_2=a_2+dy,\quad
 \psi_3=T-a_1-a_2-d(x+y).                                \qquad\text{(6.2)}
```


Restrict the first two values to coefficient boxes of radius $`H_Y/4`$
about $`T/3`$. The last is then within $`H_Y/2`$. The preimage $`\Omega`$
is convex in $`2r`$ real coordinates, and for
$`N_0=\lceil C_KY/d\rceil`$ it satisfies


```math
\Omega\subset[-N_0,N_0]^{2r},\qquad
 |\Omega|\asymp_K H_Y^{2r}/d^{2r}.                        \qquad\text{(6.3)}
```


The forms have normalized coefficient norm $`O_K(d)`$, hence bounded
by any sufficiently large fixed power of $`\log N_0`$. For every
$`i\ne j`$, the image of
$`\dot\psi_i|_{\ker\dot\psi_j}`$ is exactly $`dO_K`$, which has finite
index $`d^r`$ in $`O_K`$. This verifies KL's actual hypothesis with
fixed $`t=3`$ and fixed integer-variable count $`2r`$.

At a prime ideal $`\mathfrak p`$ not dividing $`dO_K`$, let
$`Q=N\mathfrak p`$. Changing the two variables modulo $`\mathfrak p`$
gives the same nonzero-triple counts used in GL. The normalized local
factor is


```math
\begin{cases}
  1-(Q-1)^{-2},&T=0\pmod{\mathfrak p},\\
  1+(Q-1)^{-3},&T\ne0\pmod{\mathfrak p}.
 \end{cases}                                             \qquad\text{(6.4)}
```


All norm-two primes divide $`dO_K`$. At a prime dividing $`dO_K`$,
the three fixed residues are units and its factor is
$`(1-Q^{-1})^{-3}\ge1`$. Since (6.2) is $`O_K`$-linear, KL Remark 12.3
factors the rational-prime local densities into these prime-ideal
factors, including the ramified primes. Consequently the full local
product has the positive uniform lower bound


```math
\prod_{N\mathfrak p\gt 2}
       \left(1-\frac1{(N\mathfrak p-1)^2}\right)\gt 0.        \qquad\text{(6.5)}
```


Take KL's exponent $`A'>\max(2rA+20,B+20)`$, increasing it for the fixed
coefficient constants if needed. Its error is
$`O(N_0^{2r}(\log N_0)^{-A'})=o(|\Omega|)`$.
The main coefficient also contains the fixed positive factor
$`(\mathrm{Res}_{s=1}\zeta_K(s))^{-3}`$. Hence the weighted count
is a positive multiple of (6.3).

It remains to remove proper prime-ideal powers, a step especially
necessary when the class number is greater than one. Among elements of
coefficient size $`O_K(Y)`$, only
$`O_K(Y^{r/2}(\log Y)^s)`$ have principal ideal $`\mathfrak p^k`$,
$`k\ge2`$. Indeed their ideal norms are $`O_K(Y^r)`$; the number of such
prime powers is $`O_K(Y^{r/2}\log Y)`$. A fixed principal ideal has at
most $`O_K((\log Y)^{s-1})`$ generators in that coefficient box.
For the latter assertion, each embedding is at most $`C_KY`$, the
fixed absolute norm is at least one, and therefore all its logarithmic
embedding sizes lie in a translated box of width $`O_K(\log Y)`$.
Counting the full unit lattice in that box proves the bound.

A fixed bad value of one form leaves at most $`O_K(Y^r)`$ choices in
its other $`r`$ variables. Including all three logarithmic weights,
bad tuples contribute
$`O_K(Y^{3r/2}\mathrm{polylog}Y)=o(|\Omega|)`$.
This removes even principal powers of nonprincipal prime ideals.
Zero and units have zero von Mangoldt weight. A surviving tuple has
three actual prime principal ideals and proves (6.1). QED.

This proof uses no addition of ideals and no principal generator for
$`\mathfrak q`$. Passing to the smaller ideal $`dO_K`$ is an arithmetic
congruence restriction on new targets; it never rescales any pool entry.
Two forms $`x,T-x`$ would fail the finite-cokernel condition and are not
used. The number of forms is three throughout.

## 7. Exact target lists and tensors

**Lemma GS.** Fix a tensor order $`k\ge1`$, exponents $`A,B>0`$, and a
symmetric tensor of unit classes modulo an ideal $`\mathfrak q`$ as in GT,
indexed by $`[n]^k`$, $`n\ge3`$. Let its labeled total be $`S\bmod\mathfrak q`$.
If $`\|S/n^k\|_\infty\le C_0Y`$, it lifts to a symmetric tensor of prime
elements of exact labeled total $`S`$, with every entry within
$`Y/(\log Y)^A`$ of $`S/n^k`$. Thresholds depend on fixed $`k`$, not on
the number of tensor entries. Prime targets may repeat.

**Proof.** The symmetry orbits have weights at most $`k!`$. Reserve
three of the $`n`$ constant-coordinate positions, which have weight one.
At every other orbit use GW in the coordinate corner opposite the
current discrepancy from the desired mean. Choose all $`r`$ coordinates
of the same prime in that corner, with displacement magnitude between
$`d_0/2`$ and $`d_0`$, where
$`d_0=Y/(100k!(\log Y)^A)`$. Adding an orbit of weight at most $`k!`$
keeps each discrepancy within $`[-k!d_0,k!d_0]`$.
The last three positions require a total within $`O_k(d_0)`$ of
$`3S/n^k`$; it is an element of $`O_K`$ and has the prescribed residue
sum. Apply GT with a fixed smaller window. QED.

Such a unit-residue tensor exists whenever

```math
S\equiv n^k\pmod{\mathfrak p}
       \quad\hbox{for every norm-two }\mathfrak p.           \qquad\text{(7.1)}
```

Set all but three weight-one positions to the residue of one. The
remaining three-unit equation is soluble at every residue field of
size at least three by the counts in GL. At size two it is soluble
precisely when its total is one, which is (7.1). Lift and use CRT.

The square and cube target compatibility equations can therefore use
exactly the same fixed-complexity procedure as in the quartic source:
a common row/column list for squares; one symmetric axis-target tensor
for cubes, then exact-total lists for all six slice-diagonal families,
and independent body targets. The physical realization of these
compatible values remains the controller's separate obligation.

## 8. Actual equal-gap pairs and worst-case deletion

The ideal-lattice count needed here has an elementary proof valid for
nonprincipal ideals.

**Lemma GI.** If $`d=N\mathfrak q`$ and $`L\ge d`$, a coefficient box
of side $`O_K(L)`$ contains $`O_K(L^r/d)`$ points of any coset of
$`\mathfrak q`$.

**Proof.** Since $`dO_K\subset\mathfrak q`$, the quotient
$`\mathfrak q/dO_K`$ has size $`d^{r-1}`$. In each coefficient residue
class modulo $`d`$, the box has $`O_K((L/d+1)^r)`$ integer points.
Multiply these bounds and use $`L\ge d`$. QED.

**Lemma GM (same-gap macro pairs).** Assume G and the pool of GP. Fix
$`a,B>0`$, let $`\eta=(\log R)^{-a}`$, and let
$`N\mathfrak q\le(\log R)^B`$. After arbitrary deletion of


```math
Q_{\rm del}=o\bigl(\eta^r M/(\log R)^B\bigr)               \qquad\text{(8.1)}
```


entries, every chord $`v_j`$ of GE supplies a nonzero actual gap
$`\Delta_j\in\mathfrak q`$, with


```math
\|\Delta_j-Rv_j\|_\infty=O_K(\eta R),                     \qquad\text{(8.2)}
```


and at least


```math
\gg_K \frac{\eta^r M\,N\mathfrak q}
                   {\varphi_K(\mathfrak q)^2\log R}
 \ \ge\ \frac{c_K\eta^rM}{(\log R)^{B+1}}                 \qquad\text{(8.3)}
```


disjoint actual pairs with this difference and midpoint
$`\overline p_M+O_K(\eta R)`$. The $`r`$ gap vectors remain independent,
and their matrix inverse is $`O_K(R^{-1})`$. Requested submatchings in
different reservoirs can be made disjoint if their total deletion
obeys (8.1).

**Proof.** Take the two boxes about the actual-mean endpoints from GE.
They lie strictly in the canonical domain with norm less than
$`(1-\varepsilon)B_M`$, so every prime there is in the prescribed
initial pool, including when its final norm tie is cut.
GW in the same unit class modulo $`\mathfrak q`$ gives at least
$`c_K\eta^r M/\varphi_K(\mathfrak q)`$ entries in each.
Condition (8.1) leaves a fixed fraction.

Their differences are in $`\mathfrak q`$ and in a box of radius
$`O_K(\eta R)`$ about $`Rv_j`$. Since $`\eta R`$ eventually exceeds
every fixed power of $`\log R`$, GI bounds their number by
$`O_K(\eta^rR^r/N\mathfrak q)`$. Pigeonholing all ordered endpoint
pairs and using $`M\asymp_K R^r/\log R`$ gives (8.3).
For a fixed difference each endpoint has at most one partner, and the
two endpoint boxes are disjoint. Thus these pairs already form a
matching. The midpoint and gap bounds follow from the boxes.
Independence and conditioning are stable under the $`O(\eta)`$
relative perturbations of GE. Reserve the required pairs and repeat
after their deletion. QED.

**Lemma GU (modular differences).** A residue $`u\bmod\mathfrak q`$
is a difference of two unit residues if and only if it vanishes modulo
every norm-two prime ideal dividing $`\mathfrak q`$. For every such
class the same boxes, after (8.1), give the count (8.3) of actual
equal-gap pairs with $`\Delta\equiv u\bmod\mathfrak q`$.

**Proof.** At a residue field of size at least three choose a residue
outside $`0,-u`$; it and its translate by $`u`$ are nonzero. At size
two both units are one, forcing $`u=0`$. Lift to prime-ideal powers
and apply CRT. Use these two unit classes in GM, and count differences
in a coset with GI. QED.

These modular gaps have size $`O_K(R)`$; only their midpoints have
error $`O_K(\eta R)`$. A physical argument must charge the former
size for each modular operation. No gap or endpoint is multiplied
by a unit or by an integer to create fictitious pool elements.

For an arbitrary full-rank additive gap lattice $`\Gamma`$, write its
integer coefficient matrix as $`G`$, with determinant $`d_\Gamma\ne0`$.
The adjugate identity gives $`d_\Gamma O_K\subset\Gamma`$. If modular
routing requires a further fixed ideal $`\mathfrak D`$, then
$`d_\Gamma\mathfrak D\subset\Gamma`$. GM and GU apply to that actual
ideal, principal or otherwise. They supply new physical endpoint
pairs rather than rescaled copies of previous pairs.

## 9. Quantitative interface and remaining dependencies

For fixed rank $`r`$, modulus exponent $`B`$, and endpoint exponent
$`a`$, the interface is


```math
\begin{array}{ll}
 \text{one endpoint box:}&\gg M/(\log R)^{ar+B},\\
 \text{one equal-gap matching:}&\gg M/(\log R)^{ar+B+1},\\
 \text{admissible prior deletion:}&o(M/(\log R)^{ar+B}),\\
 \text{midpoint error per pair:}&O_K(R/(\log R)^a),\\
 \text{modular increment:}&O_K(R).
 \end{array}                                               \qquad\text{(9.1)}
```


Every fixed power $`H_Y=Y/(\log Y)^A`$ is available for prime targets.
The ternary proof can take any fixed KL exponent
$`A'>\max(2rA+20,B+20)`$. All real coordinates are handled by one
prime vector or one orientation of whole elements. Arithmetic rank
does not change the two or four equal-gap pairs required by a spatial
rectangle or cuboid.

Consequently arbitrary degree and class number introduce no unresolved
analytic premise in GW, GP, GE, GL, GT, GS, GI, GM, or GU once the stated
canonical domain is established. For the energy model that domain is
supplied by the separate exact normalization proof; for the previously
frozen quartic model it was already proved.

The following are not consequences of this analytic manuscript alone:
the exact arithmetic definition of admissible orders; exclusion of
exceptional prime associates in an impossibility proof; seed-gap lattice
construction; complete bounded integer attainability; support placement,
per-line load and whole-bundle concentration; preservation of all cube
line identities; or the end-to-end array theorem. Those must be proved
in the companion [local](general_normalization_local.md),
[controller](general_controller.md), and composition sources.

All analytic thresholds retain the ineffectivity of the Siegel input.
No effective numerical cutoff, conductor-uniform statement, minimal
coefficient-height pool, or general effective boundary algorithm for a
logarithmic parallelotope is asserted. The argument concerns ordinary
sums of elements of $`O_K`$, including prime elements of non-prime
rational norm; it never replaces those sums by an addition of ideals.
