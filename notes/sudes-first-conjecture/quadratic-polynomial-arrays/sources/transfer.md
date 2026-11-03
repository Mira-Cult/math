# Smaller bounds for canonical polynomial arrays

## Result, scope, and source boundary

This public excerpt proves explicit sufficient bounds for canonical quadratic arrays over the rationals. It includes the complete quadratic argument from the frozen scientific manuscript; finite-field sections are omitted. The inputs are primitive, but the conclusion does not assert primitive integer-polynomial sums. Labels are manuscript-local. All logarithms are natural unless a base is specified.

The model is exactly
[the exact public model](../README.md#exact-pool-and-geometry).
For quadratics the inputs are the first $`n^D`$ primitive, irreducible
integer polynomials $`aX^2+bX+c`$, with $`a\gt 0`$, ordered by height and then
by the ascending coefficient tuple $`(c,b,a)`$. Representatives are never
rescaled. All


```math
L_D(n)=((n+2)^D-n^D)/2
```


full signed-coordinate lines are imposed, for $`n\ge2`$. There are no
section sums or wrapped lines. Both parities of $`n`$ are admitted in the
quadratic conclusion.

**Theorem PQ1 (canonical quadratic bounds).** The exact controller
PQ-C below is sufficient for every integer order $`n\ge2^x`$. Its smallest
accepted integer exponents include:

| Dimension $`D`$ | Previous reviewed sufficient cutoff | New sufficient cutoff |
|---:|---:|---:|
| 2 | $`2^{3072}`$ | $`2^{120}`$ |
| 3 | $`2^{4096}`$ | $`2^{67}`$ |
| 4 | $`2^{5120}`$ | $`2^{47}`$ |
| 5 | $`2^{6144}`$ | $`2^{37}`$ |
| 6 | $`2^{7168}`$ | $`2^{31}`$ |
| 10 | $`2^{11264}`$ | $`2^{21}`$ |
| 100 | $`2^{103424}`$ | $`2^{24}`$ |
| 1000 | $`2^{1025024}`$ | $`2^{27}`$ |

At every such order there is a bijective placement with all required sums
irreducible over $`\mathbb Q`$. The smallest exponent accepted by this
controller is not asserted to be the optimal existence threshold.
A simple closed sufficient bound, valid for every $`D\ge2`$, is


```math
n\ge\max\{2^{120},\,2^{24}(D+1)^2\}.       \qquad\text{(PQ-U)}
```


Exhaustive enumeration of permutations is an effective construction;
an efficient algorithm is not claimed.


The imported height-count and sampling lemmas are proved in [the baseline quadratic manuscript](characteristic_zero.md). The complete [permutation bridge](permutation_bridge.md) supplies the local-lemma argument. These public copies, the exact original inputs, and their hashes are listed in [PROVENANCE.md](../PROVENANCE.md). No private repository access is needed.

## 1. Density and actual coefficient means

Write


```math
B_H=\{(c,b,a):|b|,|c|\le H,\ 1\le a\le H\},\qquad
 V_H=H(2H+1)^2.
```


Let $`A`$ be the exact canonical prefix of size $`N=n^D`$, and $`H`$
its maximum height. Thus the prefix contains every primitive irreducible
of height at most $`H-1`$. The final height shell can be an arbitrary
initial part in its prescribed lexicographic order.

The imported characteristic-zero Lemma 1.1 proves the explicit bound


```math
R(H)\le40H^2(1+\log(2H))                         \qquad\text{(PQ1.1)}
```


for all reducibles in $`B_H`$, including nonprimitive ones. Its elementary
factor-height proof is unchanged. The final shell has at most $`12H^2`$
points.

**Lemma PQ2.** If $`H\ge2^{15}`$, then


```math
|A|\ge\frac{13}{16}V_H.                         \qquad\text{(PQ1.2)}
```


If also $`n\ge256,D\ge2`$, every population left after at most $`2n+1`$
deletions from $`A`$ has size at least $`4V_H/5`$.

**Proof.** A nonprimitive vector has a common prime divisor. A union
bound over primes therefore bounds their number by


```math
4H^3\sum_p p^{-3}+4H^2\sum_p p^{-2}+H(1+\log H).
```


All primes other than 2 and 3 occur among the odd integers at least 5.
The elementary decreasing-function integral bound gives


```math
\sum_p p^{-3}\le\frac18+\frac1{27}+\frac9{500}
                   =\frac{4861}{27000},\qquad
 \sum_p p^{-2}\le\frac14+\frac19+\frac7{50}
                   =\frac{451}{900}.                  \qquad\text{(PQ1.3)}
```


For example the tail in the first bound is at most
$`5^{-3}+\int_2^\infty(2t+1)^{-3}dt=9/500`$.
After also deleting reducibles and the entire possible last shell,


```math
\frac{V_H-|A|}{H^3}\le
 \frac{4861}{6750}
 +\frac{12151/225+40\log(2H)}{H}
 +\frac{1+\log H}{H^2}\lt \frac34.                        \qquad\text{(PQ1.4)}
```


The error terms decrease for $`H\ge2^{15}`$; at that endpoint use
$`\log(2H)\lt 16,\log H\lt 15`$ to verify the strict rational inequality.
Since $`V_H\ge4H^3`$, this implies (PQ1.2).
Also $`V_H\ge N\ge n^2`$, and


```math
\frac{2n+1}{V_H}\le\frac2n+\frac1{n^2}
                         \le\frac{513}{65536}\lt \frac1{80}.
```


The density falls from at least $`13/16`$ to at least
$`13/16-1/80=4/5`$. No deletion pattern is assumed. $`\square`$

For $`E=A`$, or $`E=A\setminus\{z\}`$ with any specified $`z\in A`$,
the same argument gives the stronger mean bounds


```math
\mu_a(E)\ge\frac{2H}{5},\qquad
 |\mu_b(E)|,|\mu_c(E)|\le17+13\log(2H).                \qquad\text{(PQ1.5)}
```


For the leading mean, put $`K=(2H+1)^2`$, and list the leading
coefficients of $`E`$ increasingly. The $`i`$-th is at least $`i/K`$.
Consequently their mean is at least $`|E|/(2K)\ge2H/5`$.
For the other two means, the primitive vectors of the complete box have
total zero in each lower coordinate by sign reflection. Removing the
reducibles, the last shell, and possibly one specified entry changes either
total in absolute value by at most


```math
H\{40H^2(1+\log(2H))+12H^2+1\}.
```


Divide by $`4V_H/5\ge16H^3/5`$ to obtain (PQ1.5).

Once the height hypothesis has been established, the useful scale bounds
are


```math
\frac{n^{D/3}}2\le H\le n^{D/3}.           \qquad\text{(PQ1.6)}
```


Indeed $`V_H\le8H^3`$ for $`H\ge2`$, and (PQ1.2) gives
$`N\ge13H^3/4\gt H^3`$. To establish the height hypothesis without circularity,
first use the unconditional $`N\le9H^3`$, hence $`H\ge n^{D/3}/3`$.

## 2. A stronger dense-box Fourier bound

**Lemma PQ3 (dense fibers).** For $`H\ge5`$ and
$`E\subset B_H`$ with $`|E|\ge4V_H/5`$, its normalized characteristic
function satisfies


```math
1-|\phi_E(t)|^2\ge\frac1{1000}
        \min\{H^2\|t\|_{\mathbb T,\infty}^2,1\}.
                                                               \qquad\text{(PQ2.1)}
```



**Proof.** First let $`F`$ be a subset of an interval of $`L\ge5`$
consecutive integers, with $`|F|\ge3L/4`$. Put $`h=\lfloor L/4\rfloor`$.
For every integer $`|v|\le h`$,


```math
|F\cap(F+v)|\ge2|F|-(L+|v|)\ge L/4.
```


Expansion by pair differences gives, with
$`D_h(\theta)=(2h+1)^{-1}\sum_{v=-h}^h e^{2\pi i v\theta}`$,


```math
1-|\phi_F(\theta)|^2
   \ge\frac{2h+1}{4L}\{1-D_h(\theta)\}.                \qquad\text{(PQ2.2)}
```


For $`\theta`$ replaced by its distance to the nearest integer,


```math
1-|D_h(\theta)|\ge\frac12
       \min\{(2h+1)^2\theta^2,1\}.                   \qquad\text{(PQ2.3)}
```


Here is an elementary verification. If $`\theta\ge1/(2h+1)`$, the sine
formula and $`\sin(\pi\theta)\ge2\theta`$ give $`|D_h|\le1/2`$.
Otherwise $`D_h\ge0`$, and


```math
1-D_h=\frac2{2h+1}\sum_{k=1}^h(1-\cos(2\pi k\theta))
       \ge\frac83h(h+1)\theta^2
       \ge\frac12(2h+1)^2\theta^2.
```


We used $`1-\cos(2\pi v)\ge8v^2`$ for $`|v|\le1/2`$.
Since $`2h+1\ge2L/5`$, (PQ2.2)--(PQ2.3) give


```math
1-|\phi_F(\theta)|\ge
           \frac1{250}\min\{L^2\theta^2,1\}.          \qquad\text{(PQ2.4)}
```



Choose a coordinate $`j`$ with maximum torus distance. Partition $`B_H`$
into coordinate-$`j`$ fibers, each of length $`L\in\{H,2H+1\}`$.
Call a fiber good if its intersection with $`E`$ has size at least
$`3L/4`$, and let $`G`$ be the number of entries of $`E`$ in good fibers.
Bad fibers contain at most three quarters of their capacity; the total
capacity of good fibers is at least $`G`$. Therefore


```math
|E|\le G+\tfrac34(V_H-G),\qquad
       \frac G{|E|}\ge\frac14.
```


Triangle inequality over fibers, followed by (PQ2.4), yields


```math
1-|\phi_E(t)|\ge\frac1{1000}
       \min\{L^2\|t_j\|_{\mathbb T}^2,1\}.
```


Now $`L\ge H`$ and $`1-|\phi_E|^2\ge1-|\phi_E|`$. $`\square`$

This replaces the source's deliberately conservative $`2^{-50}`$ gap by
$`1/1000`$. It uses the actual dense population; it does not posit
independent uniform coefficients.

## 3. Without replacement, including one specified entry

Consider either a uniform $`n`$-subset of $`A`$, or such a subset
conditioned on containing a specified $`z`$. Write its sum as $`S`$;
in the latter case first exclude $`z`$ and sum $`r=n-1`$ sampled entries,
then add $`z`$. In the former case $`r=n`$.

The source's pairing construction samples $`2r`$ distinct entries,
pairs them, and independently chooses one endpoint in each pair.
Label symmetry proves the result is a uniform $`r`$-subset. Every
residual population has density at least $`4/5`$, by Lemma PQ2.
For distinct uniform $`a,b`$ in such a population, Cauchy--Schwarz and
the exact distinct-pair identity give


```math
\mathbb E|\cos(\pi t\cdot(a-b))|
 \le\left(\frac{1+|\phi_E(t)|^2}{2}\right)^{1/2}
 \le\exp\!\left[-\frac1{4000}
      \min\{H^2\|t\|_{\mathbb T,\infty}^2,1\}\right].
```


Sequential conditioning over the chosen pairs proves


```math
|\phi_S(t)|\le
 \exp\!\left[-\frac r{4000}
      \min\{H^2\|t\|_{\mathbb T,\infty}^2,1\}\right].
                                                               \qquad\text{(PQ3.1)}
```


The fixed entry only contributes a complex factor of modulus one.

For $`n\ge256`$, $`r\ge255n/256`$. One-dimensional Fourier inversion for
any coefficient, and three-dimensional inversion for the whole sum, give


```math
\begin{split}
 \sup_v\Pr(S_c=v)&\le\frac{113}{H\sqrt n}+e^{-n/4096},\\
 \sup_w\Pr(S=w)&\le
       \frac{C_3}{H^3n^{3/2}}+e^{-n/4096},
       \qquad C_3=2\,800\,000.                        \qquad\text{(PQ3.2)}
 \end{split}
```


For clarity, the three-dimensional constant uses the actual maximum norm:


```math
\int_{\mathbb R^3}e^{-a\|t\|_\infty^2}\,dt
       =24\int_0^\infty u^2e^{-au^2}\,du
       =6\sqrt\pi\,a^{-3/2}.
```


Thus its sufficient constant is
$`48\sqrt\pi(256000/255)^{3/2}\lt C_3`$; the one-dimensional constant
is $`\sqrt{4\pi(256000/255)}\lt 113`$. Squaring and using
$`\pi\lt 22/7`$ makes both checks rational. The outside-cube contribution
in inversion is bounded by $`e^{-n/4096}`$, because
$`r/4000\ge255n/1024000\gt n/4096`$.

The source's elementary exponential-moment argument also gives, for
any $`T\gt 0`$ and


```math
u=H\sqrt{2nT},
```


a probability at most $`6e^{-T}`$ that any coefficient sum differs from
its own expectation by more than $`u`$. It applies unchanged to both
sampling laws: the sample size is at most $`n`$, every coordinate range
has length at most $`2H`$, and a fixed included entry only translates
the sum. The elementary-symmetric-mean bound pays for sampling without
replacement; no independent-line assertion is made.

## 4. Reducibility: separate zero constants from small nonzero roots

A quadratic with positive leading coefficient and zero constant
coefficient is reducible. Count this entire event using the first,
one-dimensional estimate in (PQ3.2). It is unnecessary to pay for a
three-dimensional box around it.

For the remaining reducibles the following root-sensitive bound is the
main extra saving.

**Lemma PQ4.** Suppose $`s\ge\sqrt M`$, $`J`$ has length at most $`s`$,
and a quadratic has


```math
A\in J\cap[A_{\min},M],\quad |B|,|C|\le s,\quad C\ne0,
 \qquad A_{\min}\ge s.
```


If every root has absolute value at most $`R`$, the number of reducible
integer quadratics in this window is at most


```math
R s^2(12+2\log M).               \qquad\text{(PQ4.1)}
```



**Proof.** Factor its primitive part into two primitive linear factors
with positive leading coefficients. Choose the one $`uX+v`$ with smaller
leading coefficient, and put the entire content into the other factor.
Then $`1\le u\le\sqrt M`$, and $`v\ne0`$, since $`C\ne0`$.
The root bound leaves at most $`2Ru`$ possible integer numerators $`v`$.
For a fixed $`u,v`$, the conditions on $`A=uw`$ and
$`B=uz+vw`$ leave at most $`s/u+1`$ choices for $`w`$ and
$`2s/u+1`$ choices for $`z`$. Discarding the condition on $`C`$
only increases the count. With $`m=\lfloor\sqrt M\rfloor`$, the result is
at most


```math
R\{4s^2 H_m+6sm+m(m+1)\}
 \le Rs^2\{4+2\log M+6+2\},
```


where $`H_m\le1+\log m`$, $`m\le s`$, and $`m(m+1)\le2s^2`$.
This also covers repeated rational roots and nonprimitive sums.
Gauss's lemma is used only for primitive integer factorization.
$`\square`$

Now put $`y=\log_2n`$, and define


```math
\begin{split}
 r_D&=(3^D-1)/2,&
 T&=(7y+11D+60)/10,\\
 U&=(180+7(D+3)y)/15,&
 A_0&=(783+91Dy)/30.                                  \qquad\text{(PQ4.2)}
 \end{split}
```


The subscript on $`A_0`$ distinguishes this scalar bound from the pool
and from a leading coefficient. Since
$`\log2\lt 7/10,\log3\lt 11/10,\log384\lt 6`$,


```math
T\gt \log(768nr_D).             \qquad\text{(PQ4.3)}
```


The simple sufficient mean and leading-window conditions are


```math
8A_0^2\le Tn^{2D/3-1},\qquad n\ge128T.         \qquad\text{(PQ4.4)}
```


Indeed (PQ1.5)--(PQ1.6) bound each lower-coefficient expectation in
absolute value by


```math
H\{2n^{1-D/3}A_0+1\}\le H\sqrt{2nT}=u.
```


The first term is at most $`u/(2H)`$ after normalizing by $`H`$;
the added 1 fits the other half since $`nT\ge2`$.
The leading expectation is at least $`2(n-1)H/5\ge3nH/8`$.
Set


```math
s=2u,\qquad M=nH.
```


Outside the concentration exception, $`|B|,|C|\le s`$,
the leading coefficient lies in an interval of length $`2u=s`$,
and


```math
nH/4\le A\le nH,\qquad s\le nH/4.
```


Also $`s\ge\sqrt M`$. Thus Lemma PQ4 applies.

For every root $`\alpha`$, putting $`q=s/A\le1`$ gives


```math
|\alpha|\le q+\sqrt q
 \le \min\{2,\,2^{11/4}(T/n)^{1/4}\}
 \le \min\{2,\,7(T/n)^{1/4}\}.                       \qquad\text{(PQ4.5)}
```


The two bounds in the minimum follow separately from $`q\le1`$ and
$`q\le8\sqrt{2T/n}`$. Moreover
$`12+2\log(nH)\le U`$. All estimates are uniform in the specified
included entry.

## 5. The complete local-lemma budget

Let $`\beta`$ be the maximum bad-subset probability conditioned on one
specified input, including also the unconditioned probability if desired.
Failure here means reducibility over $`\mathbb Q`$.
The permutation theorem PL at the pinned source requires


```math
8nr_D\beta\le1.              \qquad\text{(PQ5.1)}
```


Its canonical-event negative dependency graph pays for overlapping
positions and for shared input entries. It is not an ordinary
independent-line local lemma. The external input is Lu--Szekely,
Theorem 1 and Lemma 3; the exact conflict budget and the factor 8 are
proved in the pinned permutation manuscript.

Separate the four contributions to the left side of (PQ5.1):

1. **Concentration exception.** By (PQ4.3),
   $`8nr_D\,6e^{-T}\lt 1/16`$.
2. **Zero constant coefficient, local main term.** By (PQ3.2) and
   (PQ1.6), this contributes at most
   

```math
E_0=1808r_D n^{-(D/3-1/2)}.
```


3. **Nonzero rational roots, local main term.** Lemma PQ4, $`s^2=8H^2nT`$,
   and the second bound in (PQ4.5) give the bound
   

```math
E_1=896C_3 r_D T^{5/4}U n^{-(D/3-1/4)}.
```


4. **Fourier remainder.** The first bound $`R\le2`$ in (PQ4.5) yields
   

```math
E_2\le136r_DTU\,n^{2D/3+2}e^{-n/4096}.         \qquad\text{(PQ5.2)}
```


   This includes the extra one-dimensional remainder for $`C=0`$:
   $`1+16H^2nTU\le17n^{2D/3+1}TU`$.

It suffices to make $`E_0\le1/64`$, $`E_1\le7/8`$, $`E_2\le1/64`$.
Then $`8nr_D\beta\lt 31/32`$. For the last of these, a convenient sufficient
inequality is


```math
\frac n{4096}\ge
        28+\frac{11D}{5}
             +\left(\frac72+\frac{14D}{15}\right)y.   \qquad\text{(PQ5.3)}
```


Take logarithms of $`64`$ times (PQ5.2), use
$`\log8704\lt 10,\log r_D\lt (11/10)D,\log T\le T,\log U\le U`$, and
$`\log n\lt (7/10)y`$. The resulting right side is exactly the expression
in (PQ5.3).

### Exact controller PQ-C

For an integer $`D\ge2`$ and integer $`x\ge10`$, evaluate $`T,U,A_0`$
from (PQ4.2) with $`y=x`$, and put $`r=r_D`$. The following finite
integer/rational comparisons are sufficient:


```math
\begin{aligned}
 Dx&\ge51,\\
 (8A_0^2)^3&\le T^3\,2^{(2D-3)x},\\
 2^x&\ge128T,\\
 (115712r)^6&\le2^{(2D-3)x},\\
 (1024C_3rU)^{12}T^{15}&\le2^{(4D-3)x},\\
 2^x/4096&\ge
       28+11D/5+(7/2+14D/15)x.
 \end{aligned}                                                     \qquad\text{(PQ-C)}
```


The fifth comparison uses the exact identity
$`(8/7)\,896=1024`$. Raising to positive integer powers loses no
direction because all quantities are positive.

### Why these endpoint tests prove whole tails

Take any real $`y\ge x`$. The first condition ensures
$`H\ge n^{D/3}/3\ge2^{17}/3\gt 2^{15}`$.
The sampling hypotheses hold since $`n\ge2^{10}\gt 256`$.

The mean-condition ratio
$`A_0(y)^2/[T(y)2^{(2D/3-1)y}]`$ has logarithmic derivative at most


```math
2/y-(2D/3-1)\log2\lt 0
                 \quad(y\ge10,D\ge2).
```


The nonzero-root ratio $`T(y)^{5/4}U(y)2^{-(D/3-1/4)y}`$ has derivative
at most


```math
9/(4y)-(D/3-1/4)\log2\lt 0.
```


For both, $`\log2\gt 2/3`$ suffices. The zero-constant ratio is strictly
decreasing. The ratios of $`2^y`$ to $`T(y)`$ and to the positive
linear expression in (PQ5.3) are increasing, since their logarithmic
derivatives are at least $`\log2-1/y\gt 0`$.
Consequently all six conditions persist. This proves every integer
order $`n\ge2^x`$, including all intervening incomplete height shells.
It proves PQ1 by PL.

The code computes the least integer passing these sufficient conditions,
using their proved monotonicity. For the displayed dimensions it also
rejects the preceding exponent. The square's remaining bottleneck is
the nonzero-root probability bound; for $`D=100,1000`$ it is the Fourier
exponential remainder. A rejected exponent is a limitation of this
controller, not evidence of nonexistence.

### Proof of the closed bound PQ-U

At $`y=120,D=2`$, all six rational conditions pass. For fixed $`y\ge120`$,
the mean and two local-main-term ratios decrease as $`D`$ increases:
$`r_{D+1}/r_D\lt 4`$, while each increment supplies a factor at most
$`2^{-y/3}`$ in the local terms; the positive linear factors grow by
at most $`3/2`$ apiece. For the mean ratio, use
$`A_{0,D+1}/A_{0,D}\le3/2`$ and the factor $`2^{-2y/3}`$.
Thus those conditions follow from the square case.

It remains to check leading domination and the Fourier remainder.
Under PQ-U,


```math
D\lt 2^{y/2-12},\qquad y\ge120.
```


Then $`T\le2^{y/2}`$, so $`128T\le2^y`$. Also the right side
of (PQ5.3) is at most $`3Dy`$, and


```math
4096\cdot3Dy\le3y\,2^{y/2}\le2^y .
```


For the first bound, use
$`0.7y+6\le2^{y/2-1}`$ and
$`1.1D\lt 2^{y/2-1}`$.
For the second, division by $`Dy`$ bounds the linear expression by
$`28/240+2.2/120+3.5/2+14/15\lt 3`$.
Finally $`3y\le2^{y/2}`$ holds at 120 and persists since the ratio
$`2^{y/2}/y`$ is increasing there. The other exponential/linear
comparison has the same elementary derivative check.
Height and sampling are immediate. This proves the stated
closed sufficient bound without a dimension-dependent numerical search.

## 6. Content remains a separate obstruction

The new Fourier estimate strengthens, rather than removes, the source's
content warning. For a uniform unconditioned subset, $`r=n`$. For every
integer $`2\le\ell\le H`$, every nontrivial character modulo $`\ell`$
has maximum torus distance at least $`1/\ell`$. Hence (PQ3.1) and finite
Fourier inversion give


```math
\left|\Pr(S\equiv0\pmod\ell)-\ell^{-3}\right|
                           \le e^{-n/4000}.           \qquad\text{(PQ6.1)}
```


In particular the probability of a nonprimitive sum is at least


```math
1/8-e^{-n/4000}.             \qquad\text{(PQ6.2)}
```


All three coefficients being even is a content failure, although the
polynomial can be irreducible over $`\mathbb Q`$.
The argument has not conditioned on primitive *sums*. It has sampled
without replacement from the primitive *input pool*. Conflating these
two conditions would invalidate a claimed $`\mathbb Z[x]`$ theorem.


### Primary probability and algebra sources

The only non-elementary probability import used for PQ1 is the already
pinned permutation bridge, based on L. Lu and L. A. Szekely,
*Using Lovasz Local Lemma in the Space of Random Injections*,
Electronic Journal of Combinatorics 14(1) (2007), R63,
Theorem 1 and Lemma 3, printed pp. 2--4:
[author PDF](https://people.math.sc.edu/lu/papers/randinj.pdf).
The author's footer has the known volume-13 typo; the journal record
fixes volume 14. Primitive factorization uses Gauss's lemma, as in
J. S. Milne, *A Primer of Commutative Algebra*, v4.03, Section 4:
[author PDF](https://www.jmilne.org/math/xnotes/CA.pdf).
No conjecture about prime patterns or polynomial tuples is imported.
