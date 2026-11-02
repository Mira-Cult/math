# Prime targets and actual-pair supply in the quadratic plane

All labels below are manuscript-local. The target and lattice lemmas have
conventional proofs, subject to the cited analytic theorems. Review scope and
publication status are recorded in [Provenance](../PROVENANCE.md). They are interfaces for a
physical permutation controller, not by themselves array-existence theorems.
The canonical pools and line systems are defined in [PROBLEM.md](../PROBLEM.md).

## 1. Sources and the window that is actually justified

We use the following pinned primary sources.

* **K-M:** Wataru Kai, *Notes on Mitsui's Prime Number Theorem with Siegel
  zeros*, [arXiv:2209.11816v3](https://arxiv.org/pdf/2209.11816v3),
  8 September 2026, Theorem 3.1.1, Theorem 2.3.1 and Appendix A.5.
* **K-L:** Wataru Kai, *Linear patterns of prime elements in number fields*,
  [arXiv:2306.16983v5](https://arxiv.org/html/2306.16983v5), 12 March 2026,
  Theorems 6.1 and 12.1, Remarks 12.2--12.4. The versioned arXiv metadata,
  rather than the HTML renderer's displayed conversion date, fixes the version.
* **HLR:** Bingrong Huang, Jianya Liu and Zeev Rudnick, *Gaussian primes in
  almost all narrow sectors*,
  [arXiv:1903.04005v1](https://arxiv.org/html/1903.04005v1), 10 March 2019,
  Theorems 1 and 4. This is inspected for its scope, not needed by the
  constructions proved below.

Write $`K=\mathbb Q(i)`$ or $`\mathbb Q(\omega)`$, and $`O=O_K`$. All areas are
ordinary Euclidean areas under the complex embedding. K-M, specialized to
the ideal $`O`$, gives, for a convex open $`C\subset\{|z|\lt Y\}`$ and
$`\alpha\in(O/\mathfrak q)^\times`$,


```math
\sum_{\substack{\pi\in C\text{ prime element}\\
                   \pi\equiv\alpha\pmod{\mathfrak q}}}
      \log N(\pi)
 =\frac{c_K}{\varphi_K(\mathfrak q)}
   \int_C\bigl(1-\chi_{\mathfrak q}(z;\alpha)
                    |z|^{-2(1-\beta)}\bigr)\,dA
   +O_K\bigl(Y^2e^{-c\sqrt{\log Y}}\bigr).                 \qquad\text{(1)}
```


Here $`c_K=4/\pi`$ in the Gaussian case and $`6/\pi`$ in the Eisenstein
case, the exceptional term is omitted if there is no exceptional zero,
and the norm of $`\mathfrak q`$ may be at most
$`\exp(c'\sqrt{\log Y})`$ for a sufficiently small positive constant
$`c'`$ depending on the field. Constants have not been numerically evaluated.
Most importantly, the error in (1) scales with the **enclosing radius
squared**, not with $`\mathrm{area}\,(C)`$.

The exceptional character is real. Since $`\mathbb C^\times`$ is connected,
its continuous archimedean component is trivial. Consequently its value in
(1) is constant in $`z`$ for fixed $`\alpha`$. If that value is $`-1`$, the
integrand is at least one. If it is $`+1`$ and $`|z|\ge aY\gt 1`$, its lower
bound is


```math
1-(aY)^{-2(1-\beta)}.                                   \qquad\text{(2)}
```


This term must not be discarded for arbitrary pseudopolynomial moduli.
For the polynomial-logarithmic moduli used here, a standard Siegel bound
(in particular the bound recorded in K-L, Theorem 6.1) gives, for every
fixed $`\epsilon\gt 0`$,


```math
1-\beta\gg_{K,\epsilon}
          N(\mathfrak f_\chi)^{-\epsilon}.
```


If $`N(\mathfrak q)\le(\log Y)^B`$, choose
$`0\lt \epsilon\le1/(2\max(B,1))`$. Then
$`(1-\beta)\log(aY)\gg\sqrt{\log Y}`$ eventually, uniformly in the
modulus. Thus (2) tends uniformly to one. This step is **ineffective**;
neither (1) nor this manuscript supplies an explicit numerical cutoff.

**Lemma W (uniform prime boxes).** Fix $`A,B\gt 0`$, $`a\gt 0`$, and the field.
Let $`H=Y/(\log Y)^A`$. Every convex box or parallelogram of area at
least $`cH^2`$, lying in $`aY\le|z|\le Y`$ and having bounded fixed shape,
contains


```math
\gg_{K,A,B,a,c}
 \frac{H^2}{\varphi_K(\mathfrak q)\log Y}                 \qquad\text{(3)}
```


prime elements in each unit class modulo every ideal
$`N(\mathfrak q)\le(\log Y)^B`$, for all sufficiently large $`Y`$.
The threshold is uniform in the location and class, but ineffective.

**Proof.** Retain the exceptional term until the preceding estimate makes
its integrand at least $`1/2`$. The resulting main term is at least a
constant times $`Y^2/(\log Y)^{2A+B}`$. Dividing the error by this bound
gives $`O((\log Y)^{2A+B}e^{-c\sqrt{\log Y}})=o(1)`$.
The maximum weight is $`2\log Y`$. This proves (3). For a half-open or closed box, shrink to a fixed smaller open
interior box; its area retains a fixed positive fraction of the original. No count in a polynomially thin box has been asserted. QED.

HLR concerns norm annuli $`X\lt N(\mathfrak p)\le2X`$ and, for every fixed
$`\rho\lt 3/5`$, almost all angular intervals of length greater than
$`X^{-\rho}`$. Its exceptional angular set has measure tending to zero.
It does not give a bound for every adaptively selected sector, a small
radial window, or specified ideal residue classes. In the notation of
this problem $`X=B=R^2`$. We do not use this almost-all result as a uniform
reservoir or target assertion.

## 2. The genuine pool scale and its vector center

Let $`M`$ be the number of prescribed representatives, let $`B`$ be the
largest prescribed norm, and put $`R=\sqrt B`$. There is one representative
per prime ideal, since both rings have class number one. Deleting the
single ramified associate class does not change the asymptotic. Norm-order
ties contain at most the two distinct split classes; an initial segment
can therefore cut at most one such pair. The prime ideal theorem, or (1)
on the full sector followed by partial summation, gives


```math
M\sim\frac{B}{\log B},\qquad
 B\sim M\log M,\qquad R\sim\sqrt{M\log M}.                \qquad\text{(4)}
```


Inert rational prime elements have norm $`p^2`$ and are included. They are
$`O(R/\log R)`$ in number, hence lower order than (4), and their contribution
to the vector total is $`O(R^2/\log R)`$ rather than its main scale
$`R^3/\log R`$. These estimates justify asymptotic bookkeeping, not deletion
of inert entries from the prescribed permutation.

Write $`\overline z=M^{-1}\sum_{z\text{ in pool}}z`$ and let $`\theta`$ be
the sector angle, $`\pi/2`$ or $`\pi/3`$. Uniform prime density in fixed
sector regions and integration imply


```math
\frac{\overline z}{R}\longrightarrow
 \frac{2}{3\theta}\bigl(\sin\theta+i(1-\cos\theta)\bigr).  \qquad\text{(5)}
```


Indeed the area of the sector disk is $`\theta R^2/2`$, and its first
complex moment is
$`R^3(\sin\theta+i(1-\cos\theta))/3`$; fixed-region approximation and
partial summation give the same leading moment for prime representatives.
The incomplete final norm tie is negligible in this calculation.
Thus the Gaussian coordinate mean is
$`(4/(3\pi),4/(3\pi))R+o(R)`$ in basis $`(1,i)`$; the Eisenstein coordinate
mean is $`(4/(\pi\sqrt3),2/(\pi\sqrt3))R+o(R)`$ in basis $`(1,\omega)`$.
Both means stay in a fixed interior subcone of the canonical sector.

For $`M=n^D`$, the natural line mean is the **vector**
$`\mu=n\overline z`$, with magnitude $`Y\asymp nR`$.
Consequently target boxes of radius


```math
H=Y/(\log Y)^A\asymp nR/(\log n)^A                       \qquad\text{(6)}
```


are justified by Lemma W. A radius merely $`O(R)`$ is not justified by
that lemma: its relative area is only $`O(n^{-2})`$.

## 3. Fixed-complexity ternary completion, uniformly in the total

Use the fixed integral basis of $`O`$ and the corresponding coefficient
supremum norm. Changing between that norm and complex absolute value costs
only a field-dependent constant.

**Lemma T (three prime targets with exact vector total).** Fix $`A,B\gt 0`$,
the field, and a fixed compact interior annular subcone of the canonical
sector. Let $`T\in O`$ with $`T/3`$ in that subcone at scale $`Y`$. Let
$`H=Y/(\log Y)^A`$. Let $`\mathfrak q=(\kappa)`$ be an ideal of norm at most
$`(\log Y)^B`$, and prescribe unit classes $`b_1,b_2,b_3`$ modulo
$`\mathfrak q`$, whose sum is $`T`$ modulo $`\mathfrak q`$.
In the Gaussian case assume that $`(1+i)\mid\mathfrak q`$.
Then, uniformly in all these data for sufficiently large $`Y`$, there are
prime elements $`p_j`$ in the prescribed classes with


```math
p_1+p_2+p_3=T,\qquad \|p_j-T/3\|_\infty\le H.           \qquad\text{(7)}
```


This is an unconditional, ineffective eventual statement using K-L.

**Proof.** Choose representatives $`b_1,b_2`$ of size $`O(|\kappa|)`$ and
consider two variables $`x,y\in O`$, equivalently four integer variables:


```math
\psi_1=b_1+\kappa x,\quad
 \psi_2=b_2+\kappa y,\quad
 \psi_3=T-b_1-b_2-\kappa(x+y).                            \qquad\text{(8)}
```


Restrict $`\psi_1`$ and $`\psi_2`$ to coefficient boxes of radius $`H/4`$
about $`T/3`$. The third value is then within $`H/2`$ of that center. The
preimage $`\Omega`$ is a convex subset of a four-dimensional box
$`[-N,N]^4`$, with


```math
N\asymp Y/|\kappa|,\qquad
 \mathrm{Vol}\,(\Omega)\asymp H^4/|\kappa|^4.          \qquad\text{(9)}
```


The constants in (8), divided by $`N`$, and its linear coefficients are
$`O(|\kappa|)\le O((\log Y)^{B/2})`$. K-L Theorem 12.1 allows these
polynomial-logarithmic coefficient bounds and constants of size
$`N(\log N)^{A'}`$. Its parameters here are fixed: $`t=3,d=4`$.
For every distinct $`i,j`$, the restriction of $`\dot\psi_i`$ to
$`\ker\dot\psi_j`$ has image $`\kappa O`$, hence finite cokernel. This
checks its actual stronger hypothesis on integer-linear maps, not only a
suggestion of pairwise independence.

The singular series has a uniform positive lower bound. To see this
directly, consider a residue field of cardinality $`Q`$. At primes dividing
$`\kappa`$, the three fixed residues are units. At all other primes,
the number of pairs of nonzero residues $`u,v`$ with $`t-u-v\ne0`$ is


```math
\begin{cases}(Q-1)(Q-2),&t=0,\\ Q^2-3Q+3,&t\ne0.
 \end{cases}                                             \qquad\text{(10)}
```


For $`Q\gt 2`$ the normalized local factors are respectively
$`1-1/(Q-1)^2`$ and $`1+1/(Q-1)^3`$. The product of their lower bounds
converges positively, since $`\sum_{\mathfrak p}N(\mathfrak p)^{-2}`$
converges. The Gaussian field of two elements is included in
$`\mathfrak q`$ by hypothesis. No field of two elements occurs in the
Eisenstein case. CRT over prime ideals gives the claimed lower bound for
the rational-prime factors used in K-L.

Choose the error exponent $`A'`$ larger than $`4A+B+20`$, increasing it
also to accommodate the coefficient bound. K-L yields a weighted count
bounded below by a positive constant times the volume in (9), because


```math
\frac{N^4(\log N)^{-A'}}{H^4/|\kappa|^4}
       \ll (\log Y)^{4A-A'}=o(1).                         \qquad\text{(11)}
```


The contribution with a higher prime power among the three values is
negligible. There are $`O_K(Y\log Y)`$ such elements of absolute value
$`O(Y)`$; fixing any one of (8) leaves $`O_K(Y^2)`$ possible lattice points
in the enclosing domain. Multiplying by the three logarithmic weights
gives $`O_K(Y^3(\log Y)^4)`$, which is $`o(H^4/|\kappa|^4)`$ under the
displayed modulus bound. Some counted tuple therefore consists of prime
elements. Inert prime elements are not classified as higher prime powers:
their ideals are prime even though their norms are rational prime squares.
Equation (8) proves the exact sum and the prescribed classes. QED.

### Why a binary completion would be an unjustified replacement

The two forms $`x`$ and $`T-x`$ have dependent linear parts, so they fail
K-L's finite-cokernel hypothesis. The theorem above uses three primes
precisely to avoid an unproved binary Goldbach assertion. Nor does K-L
justify a number of coupled forms growing with $`n`$; all its uses here
have the same three forms.

## 4. Compatible prime target tensors without growing pattern complexity

**Lemma S (symmetric exact-total targets).** Fix $`r\ge1`$, $`A,B\gt 0`$ and
$`n\ge3`$. Let $`S\in O`$, put $`\mu=S/n^r`$, and suppose that $`\mu`$ lies
in a fixed interior annular subcone at scale $`Y\to\infty`$. Prescribe a
symmetric $`r`$-tensor of unit residues modulo $`\mathfrak q`$, of norm at
most $`(\log Y)^B`$, with labeled-position sum $`S\pmod{\mathfrak q}`$.
Include $`(1+i)`$ in $`\mathfrak q`$ in the Gaussian case. Then there is a
symmetric tensor of prime elements with exactly that total and residue
pattern, all within $`Y/(\log Y)^A`$ of $`\mu`$. The threshold is uniform
in $`n,S`$ and the pattern, with $`r,A,B`$ fixed.

**Proof.** Symmetry orbits have weights at most $`w=r!`$; the $`n`$
constant-coordinate positions have weight one. Reserve three of those
positions. Let $`d=Y/(100w(\log Y)^A)`$ and process all other orbits.
For each orbit choose a prime in its prescribed class whose two coordinate
displacements from $`\mu`$ have the signs opposite the current coordinate
discrepancies, with each magnitude in $`[d/2,d]`$. Lemma W supplies all
four corner boxes uniformly. If a coordinate discrepancy is zero either
sign is allowed. On adding an orbit of weight at most $`w`$, each
discrepancy coordinate remains in $`[-wd,wd]`$, by elementary induction.

The exact remaining total is $`T=3\mu-E\in O`$, where
$`\|E\|_\infty\le wd`$, and its prescribed three classes sum to $`T`$.
Apply Lemma T at center $`T/3`$, with radius $`d`$ (a fixed-factor change
in the logarithmic window). The three finishing primes remain within
$`d+wd/3\lt Y/(\log Y)^A`$ of $`\mu`$. No prime entry is being repeated:
these are target values, for which repetition is allowed. QED.

Unit patterns with the required totals exist in the circumstances of the
baseline odd-order pool. In a residue field with $`Q\ge3`$, (10) shows
that every residue is a sum of three nonzero residues; lift to ideal powers
and apply CRT. In the Gaussian field with $`Q=2`$, the necessary condition
for such a triple is $`T\equiv1\pmod{1+i}`$, and it is sufficient. For
a symmetric tensor set all but three weight-one positions to the unit
one and use this triple completion. The Gaussian condition becomes
$`S\equiv n^r\pmod{1+i}`$; it holds for the relevant odd $`n`$ and total
of $`n^D`$ prescribed entries. The Eisenstein construction imposes no
analogous restriction on $`n`$ at the target stage.

For sufficiently large squares, use a common length-$`n`$ vector of sum $`S`$ for the row
and column targets and choose both diagonal targets by Lemma W. For
odd-order cubes with $`n\ge11`$, use a symmetric $`n\times n`$ matrix $`P`$ of total $`S`$
as all three directional axis-target tensors. Their plane marginals agree.
For each face family apply the $`r=1`$ version with exact total equal to
the corresponding diagonal sum of $`P`$; choose the four body targets
independently. These are exactly the six additional identities in the
pinned ordinary signed-incidence theorem. All face means differ from
$`\mu`$ by at most the axis radius, so using smaller fixed-factor radii
gives a common bound $`O(Y/(\log Y)^A)`$ for every target. All operations
are equalities in $`O`$, hence in both integer coordinates simultaneously.

This establishes compatible prime-valued targets near the actual vector
mean for the baseline pools. Their realization by a permutation, including
residue routing into the trade lattice, remains a separate obligation.

## 5. Density supplies independent common differences, with disjoint pairs

This section is elementary. It does not assume Gaussian or Eisenstein
twin primes, prime-pattern asymptotics, unit rotations, or prime counts
in small boxes. Its input is the actual finite set of available points.

**Lemma G (two common gaps at one scale).** Let
$`A\subset[-U,U]^2\cap\mathbb Z^2`$, with $`m=|A|\ge U^2/L`$ and
$`L\ge2`$. Let $`d`$ be a positive integer and choose a real scale satisfying


```math
10^6dL^2\le H\le U.                                    \qquad\text{(12)}
```


There are two differences $`\delta_1,\delta_2\in d\mathbb Z^2`$ with
$`\|\delta_j\|_\infty\le H`$ and


```math
|\det(\delta_1,\delta_2)|
       \ge \frac{H^2}{10^6L^{3/2}},\qquad
 \|[\delta_1\ \delta_2]^{-1}\|_\infty
       \le\frac{2\cdot10^6L^{3/2}}H.                    \qquad\text{(13)}
```


For each direction there are at least
$`\lfloor m/(10000L)\rfloor`$ pairs $`(a,a+\delta_j)`$ from $`A`$,
and all pairs in both families can be chosen mutually disjoint.

**Proof.** Partition the coefficient plane into half-open squares of side
$`H`$, and within each square partition by the two coordinate residues
modulo $`d`$. There are at most $`16U^2d^2/H^2`$ nonempty groups. If their
sizes are $`s_g`$, the number of ordered pairs of distinct points in a group
satisfies


```math
P=\sum_g s_g(s_g-1)
   \ge \frac{m^2H^2}{16U^2d^2}-m
   \ge \frac{mH^2}{32d^2L}.                              \qquad\text{(14)}
```


Every difference belongs to $`d\mathbb Z^2\cap[-H,H]^2`$. There are
at most $`9H^2/d^2`$ possible differences. Put
$`s=H/(100\sqrt L)`$. Since $`s\ge d`$, differences of supremum norm at
most $`s`$ account for at most $`9ms^2/d^2`$ ordered pairs. Subtracting
these from (14) leaves at least $`mH^2/(64d^2L)`$ pairs, so some
$`\delta_1`$ with $`\|\delta_1\|_\infty\gt s`$ occurs at least
$`m/(576L)`$ times.

Put $`h=H/(10000L)`$. The number of lattice differences in the strip of
Euclidean distance at most $`h`$ from the real span of $`\delta_1`$ is
at most


```math
(2H/d+1)(2\sqrt2h/d+1)
 \le 9Hh/d^2+3H/d
 \lt  H^2/(64d^2L).                                        \qquad\text{(15)}
```


For the first inequality choose the coordinate where the unit direction
of $`\delta_1`$ has magnitude at least $`1/\sqrt2`$, and count the possible
values of the other coordinate for each lattice value of that one.
The final strict inequality follows from (12), with ample slack.
At most $`m`$ ordered pairs realize any one difference, so removing the
strip from (14) still leaves at least $`mH^2/(64d^2L)`$ pairs. Pigeonhole
again to obtain a $`\delta_2`$ occurring at least $`m/(576L)`$ times,
at distance greater than $`h`$ from the first span. Since
$`|\delta_1|\gt s`$, the determinant bound follows. The adjugate formula,
whose row sums are at most $`2H`$, gives the inverse bound.

For any fixed nonzero difference, its pair graph has maximum degree two.
A greedy matching therefore has at least one third as many edges. Select
$`k=\lfloor m/(10000L)\rfloor`$ disjoint pairs for $`\delta_1`$. Deleting
their $`2k`$ endpoints removes at most $`4k`$ edges from the second graph.
It retains more than $`m/(1000L)`$ edges and hence a matching of size at
least $`k`$. Both matchings use actual points of $`A`$. QED.

Repeated application tolerates arbitrary prior deletions as long as the
remaining set still satisfies $`m\ge U^2/L`$. Only the required submatching
should be reserved; reserving every pair at every scale would waste the
budget. For the canonical prime pool one can take $`U=2R`$ and
$`L=C\log R`$ with a fixed sufficiently large $`C`$, by (4). Any deletion
of $`o(M)`$ entries preserves such a density bound. In particular each
direction supplies $`\gg M/\log R`$ disjoint pairs. Four-pair cuboid
gadgets consume four members of a matching, not four occurrences with
possibly repeated endpoints.

### The generated group is a lattice, not automatically an ideal

Apply Lemma G at $`d=1`$, $`H_s=10^6L^2`$, assuming $`H_s\le U`$.
Let its two selected gaps be $`g_1,g_2`$ and set


```math
\Gamma=\mathbb Zg_1+\mathbb Zg_2,\qquad
 d_\Gamma=|\det(g_1,g_2)|\le2H_s^2.                       \qquad\text{(16)}
```


This is exactly the generated additive lattice; its index is the stated
determinant. The adjugate identity proves
$`d_\Gamma\mathbb Z^2\subset\Gamma`$. Under either integral basis this
is the genuine ideal $`(d_\Gamma)\subset O`$, of norm $`d_\Gamma^2`$.
It is a permitted polynomial-logarithmic modular refinement. No
multiplication of physical gaps is being inferred: later gaps in that
ideal come from new actual pairs, obtained by the residue partition in
Lemma G.

## 6. A finite signed prefix covering a two-dimensional correction box

The following gives an arithmetic consumer for the gap supply. It still
requires legal physical switches of the relevant incidence type, each
with the same two available orientations. That requirement is not supplied
by the lattice calculation.

**Lemma P (polynomial-logarithmic prefix).** Keep (16). Assume $`U`$ is
large enough that
$`H_{\min}=10^6d_\Gamma L^2\le U`$. Set $`H_j=U/2^j`$ and take
$`J`$ so that $`H_J\in[H_{\min},2H_{\min})`$. At each scale use Lemma G
with $`d=d_\Gamma`$ to obtain a matrix $`D_j`$ of two actual gaps in
$`d_\Gamma O\subset\Gamma`$. For every fixed $`C\gt 0`$, every
$`v\in\Gamma`$ with $`\|v\|_\infty\le CU`$ has a representation


```math
v=\sum_{j=0}^J D_j c_j+[g_1\ g_2]c_s,\qquad
             c_j,c_s\in\mathbb Z^2,                     \qquad\text{(17)}
```


with the bounds


```math
\begin{split}
 \|c_0\|_\infty&\le2\cdot10^6 C L^{3/2}+1,\\
 \|c_j\|_\infty&\le4\cdot10^6 L^{3/2}+1\quad(j\ge1),\\
 \|c_s\|_\infty&\le4\cdot10^6H_sL^2.
 \end{split}                                             \qquad\text{(18)}
```


Thus only $`O_C(L^4+L^{3/2}\log U)`$ signed copies of the selected
increments suffice to cover the entire indicated lattice box, after
reserving that many copies in each necessary direction.

**Proof.** Starting from $`v`$, at scale $`j`$ round each coordinate of
$`D_j^{-1}r`$ to the nearest integer. The new residual is in $`\Gamma`$,
and has supremum norm at most $`H_j`$, since the sum of the absolute
coordinates of either row of $`D_j`$ is at most $`2H_j`$. For $`j=0`$, (13)
gives the first coefficient bound; thereafter the previous residual is
at most $`H_{j-1}=2H_j`$, proving the second. The final residual belongs
to $`\Gamma`$, so its coordinates in the seed basis are integers.
The inverse seed matrix has norm at most $`2H_s/d_\Gamma`$ and the
residual is at most $`H_J\lt 2H_{\min}`$; this proves the last bound.
Summing the multiplicities proves the assertion. QED.

Signed capacities have a literal finite-switch implementation: if a
switch has possible actions $`0`$ and $`\delta`$, reserving $`2b`$ disjoint
copies and starting with $`b`$ in each orientation makes every integer
multiple $`c\delta`$, $`|c|\le b`$, available relative to that start.
For eight-cell cuboids each copy requires four disjoint equal-gap pairs.
The total point demand of one prefix is polynomial-logarithmic, and all
its endpoints are distinct if the required submatchings are reserved
before filler assignment. A controller must separately bound line loads,
center this chosen start, and absorb nonnative incidence effects.

## 7. Centered macroscopic and modular four-pair supply

**Lemma M (centered macroscopic gaps).** Let $`m_0`$ be the actual mean
of the canonical pool and let $`q=(d_\Gamma)`$, with
$`N(q)\le(\log R)^B`$. Fix $`c\gt 0`$ and put $`\eta=(\log R)^{-c}`$.
For either coefficient direction $`e_j`$, put $`u_j=(R/100)e_j`$.
After deletion of


```math
Q=o\left(\frac{\eta^2 M}{(\log R)^B}\right)              \qquad\text{(19)}
```


pool elements, there is a common gap $`\delta\in q\subset\Gamma`$
with


```math
\|\delta-u_j\|_\infty\le2\eta R                         \qquad\text{(20)}
```


and a matching of at least


```math
\gg \frac{\eta^2M}{(\log R)^{B+1}}                     \qquad\text{(21)}
```


actual prime pairs of that gap, all with midpoints within $`\eta R`$
of $`m_0`$. In particular any four pairs supply the equal-gap arithmetic
data of a legal eight-cell cuboid switch, once its cells are assigned.

**Proof.** Take coefficient boxes of radius $`\eta R`$ centered at
$`m_0-u_j/2`$ and $`m_0+u_j/2`$. Formula (5) ensures, for large $`R`$,
that both boxes lie strictly inside the canonical sector and inside a
disk of radius $`(1-\epsilon)R`$, for some fixed $`\epsilon\gt 0`$. Thus
every prime in them belongs to the prescribed pool, regardless of the
last norm tie. Prescribe the same unit class, for example one, modulo
$`q`$. Lemma W gives at least
$`\gg\eta^2M/\varphi_K(q)`$ primes in each box, and (19) leaves a
fixed positive fraction of these counts. The two boxes are disjoint.

There are at least $`\gg\eta^4M^2/\varphi_K(q)^2`$ ordered pairs
between the boxes. Their differences lie in the ideal lattice $`q`$ and
in a box of side $`4\eta R`$ about $`u_j`$. Since $`q`$ is a rotated
square or hexagonal lattice of spacing comparable to $`\sqrt{N(q)}`$,
there are $`O(\eta^2R^2/N(q))`$ possible differences; its polynomial-
logarithmic norm makes the boundary term smaller. Pigeonholing gives
at least


```math
\gg\frac{\eta^2M\,N(q)}{\varphi_K(q)^2\log R}
 \ge\frac{c'\eta^2M}{(\log R)^{B+1}}
```


pairs with one difference. For a fixed difference these pairs already
form a matching: each endpoint has one possible partner, and the two
boxes do not intersect. Their midpoint and gap bounds follow from the
box definitions. QED.

**Lemma U (unit differences and modular gaps).** A class
$`\Delta\pmod q`$ is the difference of two unit classes if and only if
its reduction is zero in every residue field of size two dividing $`q`$.
Consequently all classes in $`(1+i)`$ are available in the Gaussian case,
and every class is available in the Eisenstein case. For every such
$`\Delta`$ and after deletions as in (19), one can obtain four disjoint
equal-gap pairs from the pool, with actual common gap congruent to
$`\Delta\pmod q`$ and all endpoints within $`O(\eta R)`$ of $`m_0`$.

**Proof.** In a residue field with $`Q\ge3`$, choose $`a`$ outside the
at most two forbidden values $`0,-\Delta`$; then $`a`$ and
$`b=a+\Delta`$ are nonzero. In the field of two elements their
difference must be zero and that condition suffices. Lift to prime-ideal
powers and combine by CRT. Apply Lemma W in two disjoint subboxes of
radius a small fixed multiple of $`\eta R`$ near $`m_0`$, in these two
classes. The pigeonhole and matching argument of Lemma M applies to
the resulting coset of $`q`$ rather than to $`q`$ itself; it provides far
more than four pairs. QED.

These are exactly the additive difference lattices of sufficiently long
baseline pools. Gaussian differences all lie in $`(1+i)`$, and the
actual gaps between $`1+2i,2+i,2+3i`$ include $`(1,-1)`$ and $`(1,1)`$,
which generate that index-two lattice. Eisenstein differences between
$`2,3+\omega,3+2\omega`$ include $`(1,1)`$ and $`(1,2)`$, of determinant
one. This identifies additive lattices; it does not apply unit rotations
to pool elements or infer an unimplemented multiplication operation.

## 8. Budget implications and the remaining interface

At $`M=n^D`$, (4) gives $`R\asymp n^{D/2}\sqrt{\log n}`$.
For a fixed exponent $`A`$, the target radius (6) dominates the random
orientation fluctuation $`O(R\sqrt{n\log n})`$. Conversely, a physical
controller with $`K=n/(\log n)^A`$ usable macroscopic stages per line
has the appropriate scale $`KR`$ for these targets. With
$`O(n^{D-1})`$ incidence-generator types, $`O(K+\mathrm{polylog}\,n)`$
stages per type use $`O(n^D/(\log n)^A)+n^{D-1}\mathrm{polylog}\,n`$
entries. By increasing the fixed exponent this can be made smaller than
the $`\gg M/\log R`$ pair supply of any one density reservoir, even
after polynomial-logarithmic bookkeeping losses.

For example, if the largest per-type stage count is
$`K_3=n/(\log n)^{A_3}`$, a fixed number of incidence families demands
$`Q=O(M/(\log n)^{A_3})+n^{D-1}\mathrm{polylog}\,n`$ entries.
The centered supply (21) survives this entire earlier allocation whenever
$`A_3\gt 2c+B+2`$. Its midpoint error is $`O(\eta K_3R)`$ per line up to
the physical load constant; this is $`o(K_0R)`$ when
$`K_0=n/(\log n)^{A_0}`$ and $`c\gt A_0-A_3`$. These inequalities can
hold simultaneously: increase $`A_3`$ while keeping the gaps between
controller exponents fixed. Their constants need not be optimized for
an eventual theorem.

These inequalities are a consistent scale ledger, not a completed
physical controller. Its outstanding obligations are to allocate the
centered large switches and prefixes to each required incidence type;
route residues into the actual lattice $`\Gamma`$; prove disjoint placement
and centering; and show that the two coordinate corrections occur through
one legal permutation. Lemmas G, P, M and U resolve the arithmetic
increment, bounded small-correction, centered supply and modular supply
interfaces. Lemmas W, T and S
resolve the analytic target interface at logarithmically relative widths.
No binary Goldbach conjecture or fixed-gap prime conjecture occurs in
those proved interfaces.

## Publication cross-reference: even Eisenstein cubes

The initial cube target discussion in Section 4 is stated for odd orders.
For the all-integer Eisenstein conclusion, use the even-order integer-image
extension and compatible-target construction in
[local arithmetic](local_arithmetic.md), together with the even-order physical
geometry in the [vector controller](vector_controller.md). The complete
composition is Theorem QPA there, not an assertion that an odd-order-only
lemma alone proves the even case.
