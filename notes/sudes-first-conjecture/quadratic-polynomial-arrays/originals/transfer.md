# Smaller bounds for canonical polynomial arrays

## Result, scope, and source boundary

This manuscript proves a stronger sufficient bound for the canonical
quadratic problem over \(\mathbb Q\), and a smaller sufficient bound for
the binary exceptional-line subsystem. It does not prove primitive
\(\mathbb Z[x]\) sums or complete eventual arrays over a fixed finite
field. Labels here are manuscript-local.

The model is exactly
[PR84's problem statement](https://github.com/Mira-Cult/math-wip/blob/3ea1a0389c2165a71d5abedf6b4c036f8b9f0166/problems/prescribed-prime-polynomials/PROBLEM.md).
For quadratics the inputs are the first \(n^D\) primitive, irreducible
integer polynomials \(aX^2+bX+c\), with \(a>0\), ordered by height and then
by the ascending coefficient tuple \((c,b,a)\). Representatives are never
rescaled. All
\[
             L_D(n)=((n+2)^D-n^D)/2
\]
full signed-coordinate lines are imposed, for \(n\ge2\). There are no
section sums or wrapped lines. Both parities of \(n\) are admitted in the
quadratic conclusion.

**Theorem PQ1 (canonical quadratic bounds).** The exact controller
PQ-C below is sufficient for every integer order \(n\ge2^x\). Its smallest
accepted integer exponents include:

| Dimension \(D\) | Previous reviewed sufficient cutoff | New sufficient cutoff |
|---:|---:|---:|
| 2 | \(2^{3072}\) | \(2^{120}\) |
| 3 | \(2^{4096}\) | \(2^{67}\) |
| 4 | \(2^{5120}\) | \(2^{47}\) |
| 5 | \(2^{6144}\) | \(2^{37}\) |
| 6 | \(2^{7168}\) | \(2^{31}\) |
| 10 | \(2^{11264}\) | \(2^{21}\) |
| 100 | \(2^{103424}\) | \(2^{24}\) |
| 1000 | \(2^{1025024}\) | \(2^{27}\) |

At every such order there is a bijective placement with all required sums
irreducible over \(\mathbb Q\). The smallest exponent accepted by this
controller is not asserted to be the optimal existence threshold.
A simple closed sufficient bound, valid for every \(D\ge2\), is
\[
              n\ge\max\{2^{120},\,2^{24}(D+1)^2\}.       \tag{PQ-U}
\]
Exhaustive enumeration of permutations is an effective construction;
an efficient algorithm is not claimed.

**Theorem PF1 (binary exceptional subsystem).** Keep the prime field
\(\mathbb F_2\) fixed and retain exactly its first \(n^D\) monic
irreducibles, ordered by degree and integer encoding, including \(X,X+1\).
One can place them so that every full signed line through \(X\) or
\(X+1\) has irreducible sum in either of the following ranges:

* \(D=2\), every odd \(n\ge9\);
* \(D\ge3\), every odd \(n\ge2D-1\).

The two entries are incident only to their \(2D\) axis lines in total,
and share no required line. All other cells can be filled with the
remaining entries arbitrarily without changing those successful lines.
This is a subsystem theorem. For example, at \(D=3,n=5\) it controls six
of the 109 required lines. It does not assert that the other 103 sums are
irreducible.

The previous canonical F2-S bound was odd \(n\ge64D\), with a sharper
per-instance invoice. PF1 improves the actual invoice and proves complete
tails; it is not based on sampled endpoints. The independently checked
complete binary squares at orders 5 and 7 in PR84 remain separate finite
results; the new analytic subsystem proof does not reclassify those
certificates or claim its own invoice passes at those orders.

### Frozen imported sources

The quadratic height count, sampling-pair construction, and permutation
local lemma are imported from the following exact PR84 scientific source:
\[
             \text{math-wip }3ea1a0389c2165a71d5abedf6b4c036f8b9f0166.
\]
The source audit containing the later fresh-pair discussion is pinned at
\[
             158baa7c6122abde0b0aee42abb502477c04088f.
\]
PR84's reviewed delivery is
3a4c5ade1b8762f3a0d982a1a448215a930179fc. Its relevant scientific files,
except the separately pinned auxiliary audit, are byte-identical to the
main scientific source.

| Imported file under problems/prescribed-prime-polynomials | SHA-256 |
|---|---|
| manuscripts/characteristic_zero.md | 3865e5685c515261eb3426fc6c2d42795b68203f8a2b2264c6d13c2074140604 |
| manuscripts/permutation_bridge.md | 3eb52979c6a822f34a784180f18eca1e316c19eaba782671e1bdbaa57be323b3 |
| manuscripts/finite_fields.md | 3407e1aac786cf12b6819d58709f2f1f72bb7bc39dd7c33a0dc49644325c460e |
| manuscripts/sources_and_controls.md, auxiliary pin | 68399ace8d134ce53bd755ab799b34c947e59d416a09aab0fec4792419a2b94b |
| code/track_a_bounds.py | 8bd2aa13245d75b4fa9d43843bddeaf40524e8ce62c7efe8504c2ba1fdabe8a7 |

The new proof is not obtained by inserting the integer-square cutoff 2001
into a polynomial theorem. The square campaign motivates paying for actual
means, actual geometry and stage-specific resources. Its prime tables,
ordered central stock, and integer target supply are not hypotheses here.

## 1. Density and actual coefficient means

Write
\[
 B_H=\{(c,b,a):|b|,|c|\le H,\ 1\le a\le H\},\qquad
 V_H=H(2H+1)^2.
\]
Let \(A\) be the exact canonical prefix of size \(N=n^D\), and \(H\)
its maximum height. Thus the prefix contains every primitive irreducible
of height at most \(H-1\). The final height shell can be an arbitrary
initial part in its prescribed lexicographic order.

The imported characteristic-zero Lemma 1.1 proves the explicit bound
\[
       R(H)\le40H^2(1+\log(2H))                         \tag{PQ1.1}
\]
for all reducibles in \(B_H\), including nonprimitive ones. Its elementary
factor-height proof is unchanged. The final shell has at most \(12H^2\)
points.

**Lemma PQ2.** If \(H\ge2^{15}\), then
\[
       |A|\ge\frac{13}{16}V_H.                         \tag{PQ1.2}
\]
If also \(n\ge256,D\ge2\), every population left after at most \(2n+1\)
deletions from \(A\) has size at least \(4V_H/5\).

**Proof.** A nonprimitive vector has a common prime divisor. A union
bound over primes therefore bounds their number by
\[
 4H^3\sum_p p^{-3}+4H^2\sum_p p^{-2}+H(1+\log H).
\]
All primes other than 2 and 3 occur among the odd integers at least 5.
The elementary decreasing-function integral bound gives
\[
 \sum_p p^{-3}\le\frac18+\frac1{27}+\frac9{500}
                   =\frac{4861}{27000},\qquad
 \sum_p p^{-2}\le\frac14+\frac19+\frac7{50}
                   =\frac{451}{900}.                  \tag{PQ1.3}
\]
For example the tail in the first bound is at most
\(5^{-3}+\int_2^\infty(2t+1)^{-3}dt=9/500\).
After also deleting reducibles and the entire possible last shell,
\[
 \frac{V_H-|A|}{H^3}\le
 \frac{4861}{6750}
 +\frac{12151/225+40\log(2H)}{H}
 +\frac{1+\log H}{H^2}<\frac34.                        \tag{PQ1.4}
\]
The error terms decrease for \(H\ge2^{15}\); at that endpoint use
\(\log(2H)<16,\log H<15\) to verify the strict rational inequality.
Since \(V_H\ge4H^3\), this implies (PQ1.2).
Also \(V_H\ge N\ge n^2\), and
\[
       \frac{2n+1}{V_H}\le\frac2n+\frac1{n^2}
                         \le\frac{513}{65536}<\frac1{80}.
 \]
The density falls from at least \(13/16\) to at least
\(13/16-1/80=4/5\). No deletion pattern is assumed. \(\square\)

For \(E=A\), or \(E=A\setminus\{z\}\) with any specified \(z\in A\),
the same argument gives the stronger mean bounds
\[
 \mu_a(E)\ge\frac{2H}{5},\qquad
 |\mu_b(E)|,|\mu_c(E)|\le17+13\log(2H).                \tag{PQ1.5}
\]
For the leading mean, put \(K=(2H+1)^2\), and list the leading
coefficients of \(E\) increasingly. The \(i\)-th is at least \(i/K\).
Consequently their mean is at least \(|E|/(2K)\ge2H/5\).
For the other two means, the primitive vectors of the complete box have
total zero in each lower coordinate by sign reflection. Removing the
reducibles, the last shell, and possibly one specified entry changes either
total in absolute value by at most
\[
       H\{40H^2(1+\log(2H))+12H^2+1\}.
\]
Divide by \(4V_H/5\ge16H^3/5\) to obtain (PQ1.5).

Once the height hypothesis has been established, the useful scale bounds
are
\[
           \frac{n^{D/3}}2\le H\le n^{D/3}.           \tag{PQ1.6}
\]
Indeed \(V_H\le8H^3\) for \(H\ge2\), and (PQ1.2) gives
\(N\ge13H^3/4>H^3\). To establish the height hypothesis without circularity,
first use the unconditional \(N\le9H^3\), hence \(H\ge n^{D/3}/3\).

## 2. A stronger dense-box Fourier bound

**Lemma PQ3 (dense fibers).** For \(H\ge5\) and
\(E\subset B_H\) with \(|E|\ge4V_H/5\), its normalized characteristic
function satisfies
\[
 1-|\phi_E(t)|^2\ge\frac1{1000}
        \min\{H^2\|t\|_{\mathbb T,\infty}^2,1\}.
                                                               \tag{PQ2.1}
\]

**Proof.** First let \(F\) be a subset of an interval of \(L\ge5\)
consecutive integers, with \(|F|\ge3L/4\). Put \(h=\lfloor L/4\rfloor\).
For every integer \(|v|\le h\),
\[
        |F\cap(F+v)|\ge2|F|-(L+|v|)\ge L/4.
\]
Expansion by pair differences gives, with
\(D_h(\theta)=(2h+1)^{-1}\sum_{v=-h}^h e^{2\pi i v\theta}\),
\[
 1-|\phi_F(\theta)|^2
   \ge\frac{2h+1}{4L}\{1-D_h(\theta)\}.                \tag{PQ2.2}
\]
For \(\theta\) replaced by its distance to the nearest integer,
\[
 1-|D_h(\theta)|\ge\frac12
       \min\{(2h+1)^2\theta^2,1\}.                   \tag{PQ2.3}
\]
Here is an elementary verification. If \(\theta\ge1/(2h+1)\), the sine
formula and \(\sin(\pi\theta)\ge2\theta\) give \(|D_h|\le1/2\).
Otherwise \(D_h\ge0\), and
\[
 1-D_h=\frac2{2h+1}\sum_{k=1}^h(1-\cos(2\pi k\theta))
       \ge\frac83h(h+1)\theta^2
       \ge\frac12(2h+1)^2\theta^2.
\]
We used \(1-\cos(2\pi v)\ge8v^2\) for \(|v|\le1/2\).
Since \(2h+1\ge2L/5\), (PQ2.2)--(PQ2.3) give
\[
     1-|\phi_F(\theta)|\ge
           \frac1{250}\min\{L^2\theta^2,1\}.          \tag{PQ2.4}
\]

Choose a coordinate \(j\) with maximum torus distance. Partition \(B_H\)
into coordinate-\(j\) fibers, each of length \(L\in\{H,2H+1\}\).
Call a fiber good if its intersection with \(E\) has size at least
\(3L/4\), and let \(G\) be the number of entries of \(E\) in good fibers.
Bad fibers contain at most three quarters of their capacity; the total
capacity of good fibers is at least \(G\). Therefore
\[
       |E|\le G+\tfrac34(V_H-G),\qquad
       \frac G{|E|}\ge\frac14.
\]
Triangle inequality over fibers, followed by (PQ2.4), yields
\[
   1-|\phi_E(t)|\ge\frac1{1000}
       \min\{L^2\|t_j\|_{\mathbb T}^2,1\}.
\]
Now \(L\ge H\) and \(1-|\phi_E|^2\ge1-|\phi_E|\). \(\square\)

This replaces the source's deliberately conservative \(2^{-50}\) gap by
\(1/1000\). It uses the actual dense population; it does not posit
independent uniform coefficients.

## 3. Without replacement, including one specified entry

Consider either a uniform \(n\)-subset of \(A\), or such a subset
conditioned on containing a specified \(z\). Write its sum as \(S\);
in the latter case first exclude \(z\) and sum \(r=n-1\) sampled entries,
then add \(z\). In the former case \(r=n\).

The source's pairing construction samples \(2r\) distinct entries,
pairs them, and independently chooses one endpoint in each pair.
Label symmetry proves the result is a uniform \(r\)-subset. Every
residual population has density at least \(4/5\), by Lemma PQ2.
For distinct uniform \(a,b\) in such a population, Cauchy--Schwarz and
the exact distinct-pair identity give
\[
 \mathbb E|\cos(\pi t\cdot(a-b))|
 \le\left(\frac{1+|\phi_E(t)|^2}{2}\right)^{1/2}
 \le\exp\!\left[-\frac1{4000}
      \min\{H^2\|t\|_{\mathbb T,\infty}^2,1\}\right].
\]
Sequential conditioning over the chosen pairs proves
\[
 |\phi_S(t)|\le
 \exp\!\left[-\frac r{4000}
      \min\{H^2\|t\|_{\mathbb T,\infty}^2,1\}\right].
                                                               \tag{PQ3.1}
\]
The fixed entry only contributes a complex factor of modulus one.

For \(n\ge256\), \(r\ge255n/256\). One-dimensional Fourier inversion for
any coefficient, and three-dimensional inversion for the whole sum, give
\[
 \begin{split}
 \sup_v\Pr(S_c=v)&\le\frac{113}{H\sqrt n}+e^{-n/4096},\\
 \sup_w\Pr(S=w)&\le
       \frac{C_3}{H^3n^{3/2}}+e^{-n/4096},
       \qquad C_3=2\,800\,000.                        \tag{PQ3.2}
 \end{split}
\]
For clarity, the three-dimensional constant uses the actual maximum norm:
\[
 \int_{\mathbb R^3}e^{-a\|t\|_\infty^2}\,dt
       =24\int_0^\infty u^2e^{-au^2}\,du
       =6\sqrt\pi\,a^{-3/2}.
\]
Thus its sufficient constant is
\(48\sqrt\pi(256000/255)^{3/2}<C_3\); the one-dimensional constant
is \(\sqrt{4\pi(256000/255)}<113\). Squaring and using
\(\pi<22/7\) makes both checks rational. The outside-cube contribution
in inversion is bounded by \(e^{-n/4096}\), because
\(r/4000\ge255n/1024000>n/4096\).

The source's elementary exponential-moment argument also gives, for
any \(T>0\) and
\[
                     u=H\sqrt{2nT},
\]
a probability at most \(6e^{-T}\) that any coefficient sum differs from
its own expectation by more than \(u\). It applies unchanged to both
sampling laws: the sample size is at most \(n\), every coordinate range
has length at most \(2H\), and a fixed included entry only translates
the sum. The elementary-symmetric-mean bound pays for sampling without
replacement; no independent-line assertion is made.

## 4. Reducibility: separate zero constants from small nonzero roots

A quadratic with positive leading coefficient and zero constant
coefficient is reducible. Count this entire event using the first,
one-dimensional estimate in (PQ3.2). It is unnecessary to pay for a
three-dimensional box around it.

For the remaining reducibles the following root-sensitive bound is the
main extra saving.

**Lemma PQ4.** Suppose \(s\ge\sqrt M\), \(J\) has length at most \(s\),
and a quadratic has
\[
 A\in J\cap[A_{\min},M],\quad |B|,|C|\le s,\quad C\ne0,
 \qquad A_{\min}\ge s.
\]
If every root has absolute value at most \(R\), the number of reducible
integer quadratics in this window is at most
\[
                    R s^2(12+2\log M).               \tag{PQ4.1}
\]

**Proof.** Factor its primitive part into two primitive linear factors
with positive leading coefficients. Choose the one \(uX+v\) with smaller
leading coefficient, and put the entire content into the other factor.
Then \(1\le u\le\sqrt M\), and \(v\ne0\), since \(C\ne0\).
The root bound leaves at most \(2Ru\) possible integer numerators \(v\).
For a fixed \(u,v\), the conditions on \(A=uw\) and
\(B=uz+vw\) leave at most \(s/u+1\) choices for \(w\) and
\(2s/u+1\) choices for \(z\). Discarding the condition on \(C\)
only increases the count. With \(m=\lfloor\sqrt M\rfloor\), the result is
at most
\[
 R\{4s^2 H_m+6sm+m(m+1)\}
 \le Rs^2\{4+2\log M+6+2\},
\]
where \(H_m\le1+\log m\), \(m\le s\), and \(m(m+1)\le2s^2\).
This also covers repeated rational roots and nonprimitive sums.
Gauss's lemma is used only for primitive integer factorization.
\(\square\)

Now put \(y=\log_2n\), and define
\[
 \begin{split}
 r_D&=(3^D-1)/2,&
 T&=(7y+11D+60)/10,\\
 U&=(180+7(D+3)y)/15,&
 A_0&=(783+91Dy)/30.                                  \tag{PQ4.2}
 \end{split}
\]
The subscript on \(A_0\) distinguishes this scalar bound from the pool
and from a leading coefficient. Since
\(\log2<7/10,\log3<11/10,\log384<6\),
\[
                         T>\log(768nr_D).             \tag{PQ4.3}
\]
The simple sufficient mean and leading-window conditions are
\[
       8A_0^2\le Tn^{2D/3-1},\qquad n\ge128T.         \tag{PQ4.4}
\]
Indeed (PQ1.5)--(PQ1.6) bound each lower-coefficient expectation in
absolute value by
\[
       H\{2n^{1-D/3}A_0+1\}\le H\sqrt{2nT}=u.
\]
The first term is at most \(u/(2H)\) after normalizing by \(H\);
the added 1 fits the other half since \(nT\ge2\).
The leading expectation is at least \(2(n-1)H/5\ge3nH/8\).
Set
\[
                         s=2u,\qquad M=nH.
\]
Outside the concentration exception, \(|B|,|C|\le s\),
the leading coefficient lies in an interval of length \(2u=s\),
and
\[
                    nH/4\le A\le nH,\qquad s\le nH/4.
\]
Also \(s\ge\sqrt M\). Thus Lemma PQ4 applies.

For every root \(\alpha\), putting \(q=s/A\le1\) gives
\[
 |\alpha|\le q+\sqrt q
 \le \min\{2,\,2^{11/4}(T/n)^{1/4}\}
 \le \min\{2,\,7(T/n)^{1/4}\}.                       \tag{PQ4.5}
\]
The two bounds in the minimum follow separately from \(q\le1\) and
\(q\le8\sqrt{2T/n}\). Moreover
\(12+2\log(nH)\le U\). All estimates are uniform in the specified
included entry.

## 5. The complete local-lemma budget

Let \(\beta\) be the maximum bad-subset probability conditioned on one
specified input, including also the unconditioned probability if desired.
Failure here means reducibility over \(\mathbb Q\).
The permutation theorem PL at the pinned source requires
\[
                         8nr_D\beta\le1.              \tag{PQ5.1}
\]
Its canonical-event negative dependency graph pays for overlapping
positions and for shared input entries. It is not an ordinary
independent-line local lemma. The external input is Lu--Szekely,
Theorem 1 and Lemma 3; the exact conflict budget and the factor 8 are
proved in the pinned permutation manuscript.

Separate the four contributions to the left side of (PQ5.1):

1. **Concentration exception.** By (PQ4.3),
   \(8nr_D\,6e^{-T}<1/16\).
2. **Zero constant coefficient, local main term.** By (PQ3.2) and
   (PQ1.6), this contributes at most
   \[
             E_0=1808r_D n^{-(D/3-1/2)}.
   \]
3. **Nonzero rational roots, local main term.** Lemma PQ4, \(s^2=8H^2nT\),
   and the second bound in (PQ4.5) give the bound
   \[
       E_1=896C_3 r_D T^{5/4}U n^{-(D/3-1/4)}.
   \]
4. **Fourier remainder.** The first bound \(R\le2\) in (PQ4.5) yields
   \[
       E_2\le136r_DTU\,n^{2D/3+2}e^{-n/4096}.         \tag{PQ5.2}
   \]
   This includes the extra one-dimensional remainder for \(C=0\):
   \(1+16H^2nTU\le17n^{2D/3+1}TU\).

It suffices to make \(E_0\le1/64\), \(E_1\le7/8\), \(E_2\le1/64\).
Then \(8nr_D\beta<31/32\). For the last of these, a convenient sufficient
inequality is
\[
 \frac n{4096}\ge
        28+\frac{11D}{5}
             +\left(\frac72+\frac{14D}{15}\right)y.   \tag{PQ5.3}
\]
Take logarithms of \(64\) times (PQ5.2), use
\(\log8704<10,\log r_D<(11/10)D,\log T\le T,\log U\le U\), and
\(\log n<(7/10)y\). The resulting right side is exactly the expression
in (PQ5.3).

### Exact controller PQ-C

For an integer \(D\ge2\) and integer \(x\ge10\), evaluate \(T,U,A_0\)
from (PQ4.2) with \(y=x\), and put \(r=r_D\). The following finite
integer/rational comparisons are sufficient:
\[
 \begin{array}{rl}
 Dx&\ge51,\\
 (8A_0^2)^3&\le T^3\,2^{(2D-3)x},\\
 2^x&\ge128T,\\
 (115712r)^6&\le2^{(2D-3)x},\\
 (1024C_3rU)^{12}T^{15}&\le2^{(4D-3)x},\\
 2^x/4096&\ge
       28+11D/5+(7/2+14D/15)x.
 \end{array}                                                     \tag{PQ-C}
\]
The fifth comparison uses the exact identity
\((8/7)\,896=1024\). Raising to positive integer powers loses no
direction because all quantities are positive.

### Why these endpoint tests prove whole tails

Take any real \(y\ge x\). The first condition ensures
\(H\ge n^{D/3}/3\ge2^{17}/3>2^{15}\).
The sampling hypotheses hold since \(n\ge2^{10}>256\).

The mean-condition ratio
\(A_0(y)^2/[T(y)2^{(2D/3-1)y}]\) has logarithmic derivative at most
\[
                 2/y-(2D/3-1)\log2<0
                 \quad(y\ge10,D\ge2).
\]
The nonzero-root ratio \(T(y)^{5/4}U(y)2^{-(D/3-1/4)y}\) has derivative
at most
\[
                 9/(4y)-(D/3-1/4)\log2<0.
\]
For both, \(\log2>2/3\) suffices. The zero-constant ratio is strictly
decreasing. The ratios of \(2^y\) to \(T(y)\) and to the positive
linear expression in (PQ5.3) are increasing, since their logarithmic
derivatives are at least \(\log2-1/y>0\).
Consequently all six conditions persist. This proves every integer
order \(n\ge2^x\), including all intervening incomplete height shells.
It proves PQ1 by PL.

The code computes the least integer passing these sufficient conditions,
using their proved monotonicity. For the displayed dimensions it also
rejects the preceding exponent. The square's remaining bottleneck is
the nonzero-root probability bound; for \(D=100,1000\) it is the Fourier
exponential remainder. A rejected exponent is a limitation of this
controller, not evidence of nonexistence.

### Proof of the closed bound PQ-U

At \(y=120,D=2\), all six rational conditions pass. For fixed \(y\ge120\),
the mean and two local-main-term ratios decrease as \(D\) increases:
\(r_{D+1}/r_D<4\), while each increment supplies a factor at most
\(2^{-y/3}\) in the local terms; the positive linear factors grow by
at most \(3/2\) apiece. For the mean ratio, use
\(A_{0,D+1}/A_{0,D}\le3/2\) and the factor \(2^{-2y/3}\).
Thus those conditions follow from the square case.

It remains to check leading domination and the Fourier remainder.
Under PQ-U,
\[
                  D<2^{y/2-12},\qquad y\ge120.
\]
Then \(T\le2^{y/2}\), so \(128T\le2^y\). Also the right side
of (PQ5.3) is at most \(3Dy\), and
\[
       4096\cdot3Dy\le3y\,2^{y/2}\le2^y .
\]
For the first bound, use
\(0.7y+6\le2^{y/2-1}\) and
\(1.1D<2^{y/2-1}\).
For the second, division by \(Dy\) bounds the linear expression by
\(28/240+2.2/120+3.5/2+14/15<3\).
Finally \(3y\le2^{y/2}\) holds at 120 and persists since the ratio
\(2^{y/2}/y\) is increasing there. The other exponential/linear
comparison has the same elementary derivative check.
Height and sampling are immediate. This proves the stated
closed sufficient bound without a dimension-dependent numerical search.

## 6. Content remains a separate obstruction

The new Fourier estimate strengthens, rather than removes, the source's
content warning. For a uniform unconditioned subset, \(r=n\). For every
integer \(2\le\ell\le H\), every nontrivial character modulo \(\ell\)
has maximum torus distance at least \(1/\ell\). Hence (PQ3.1) and finite
Fourier inversion give
\[
 \left|\Pr(S\equiv0\pmod\ell)-\ell^{-3}\right|
                           \le e^{-n/4000}.           \tag{PQ6.1}
\]
In particular the probability of a nonprimitive sum is at least
\[
                         1/8-e^{-n/4000}.             \tag{PQ6.2}
\]
All three coefficients being even is a content failure, although the
polynomial can be irreducible over \(\mathbb Q\).
The argument has not conditioned on primitive *sums*. It has sampled
without replacement from the primitive *input pool*. Conflating these
two conditions would invalidate a claimed \(\mathbb Z[x]\) theorem.

## 7. A fixed-binary-field transfer with an exact resource invoice

Let \(m\) be the actual highest degree in the canonical binary prefix.
The exact complete-shell counts satisfy
\[
 2^j=\sum_{d\mid j}dI_2(d),\qquad
 \sum_{j<m}I_2(j)<N\le\sum_{j\le m}I_2(j).             \tag{PF7.1}
\]
The source proves, for \(N\ge16\),
\[
                         2^{m+1}<16N\log_2N.         \tag{PF7.2}
\]
No uniformity of the unfinished degree shell is assumed.

Every input other than \(X,X+1\) has evaluation vector \((1,1)\)
at \(0,1\). These inputs therefore lie in one affine coset \(C\)
of the kernel of the two independent evaluation maps on polynomials
of degree at most \(m\). This coset has exactly
\[
                          W=2^{m-1}                 \tag{PF7.3}
\]
elements. After any deletions the remaining nonexceptional inputs
remain in this same coset. Translating it to its underlying vector
space preserves every even-cardinality zero-XOR equation, and also
each equation in which an odd-cardinality set sums to one selected
entry.

The elementary Cauchy--Schwarz/deletion proof in the source's F2-Z
therefore gives the following exact supplies for every remaining
set of size \(R\), now with ambient order \(W\):

| Required object | Sufficient strict condition |
|---|---:|
| Four distinct entries with XOR zero | \(R^2>6W\) |
| Six distinct entries with XOR zero | \(R^2>15W\) |
| One entry \(f\), with two disjoint three-sets outside \(f\), each summing to \(f\) | \(R^2>15W\) |
| One entry \(f\), with two disjoint five-sets outside \(f\), each summing to \(f\) | \(R^2>40W\) |

For completeness, ordered even \(k\)-tuples with XOR zero number at
least \(R^k/W\). Tuples with a specified equal pair number at most
\(R^{k-2}\), so at least
\(R^k/W-\binom{k}{2}R^{k-2}\) have all entries distinct.
If a fixed \(f\) has no two disjoint \((k-1)\)-sets summing to it,
one such set meets every other; counting those intersections gives
at most \((k-1)^2R^{k-2}\) distinct ordered tuples in total.
The thresholds are therefore \(\binom{k}{2}\) for zero sets, and
\(\binom{k}{2}+(k-1)^2\) for the paired sets, at \(k=4,6\).
All selections can be found by exhaustive finite search.

### Geometry with only the required axis lines through the exceptions

For \(n\ge2D-1\), put
\[
 a=(1,2,\ldots,D),\qquad
 b=(n-D+1,n-D+2,\ldots,n).
\]
Coordinates within either point are distinct. No two coordinates of
\(a\) or of \(b\) sum to \(n+1\): the former sums are at most \(2D-1\le n\),
and the latter sums are at least \(2n-2D+3>n+1\).
Thus neither point lies on a full signed line varying two or more
coordinates. Also \(a_i\ne b_i\) for every \(i\), in our stated ranges.
They share no axis line.

For \(D\ge3\) their axis stars are disjoint, since two different
axis directions leave some coordinate fixed at different values.
Within either star the lines meet only at their center. For \(D=2\)
there are exactly two cross-intersection cells, as in the source.
Place \(X\) at \(a\) and \(X+1\) at \(b\).

### Dimensions at least three

Put \(R=N-2-2D(n-1)\). There are \(2D\) disjoint noncentral sets
of \(n-1\) cells to fill with zero-XOR inputs. For \(n\equiv1\pmod4\)
use zero four-sets; for \(n\equiv3\pmod4\) use one zero six-set per
line and then zero four-sets. Reserving every chosen entry immediately
makes the construction valid under
\[
 R>0,\qquad
 R^2>c_nW,\quad
 c_n=\begin{cases}6,&n\equiv1\pmod4,\\15,&n\equiv3\pmod4.\end{cases}
                                                               \tag{PF7.4}
\]
The old uniform constant 40 is unnecessary for these disjoint stars.

Here is a complete tail proof, not just an asymptotic estimate.
For \(n\ge5,D\ge3\), the deletion proportion
\((2+2D(n-1))/n^D\) decreases in \(D\) and is at most
\(6/n^2\le6/25<1/4\). Hence \(R\ge3N/4\).
Also \(N/D\ge n^3/3\), because \(n^D/D\) increases for \(D\ge3\).
By (PF7.2)--(PF7.3), \(W<4ND\log_2n\).
It follows that (PF7.4), even with the larger constant 15, holds whenever
\[
                         n^3>320\log_2n.
 \]
This holds for every \(n\ge11\): at 11 use
\(\log_2 11<7/2\), and \(n^3/\log_2n\) increases thereafter.
For \(n=5,7,9\), the geometry \(D\le(n+1)/2\) leaves exactly these
six finite cases:

| \(n,D\) | Highest degree \(m\) | \(R^2\) | Required strict lower bound \(c_n2^{m-1}\) |
|---|---:|---:|---:|
| 5,3 | 9 | 9801 | 1536 |
| 7,3 | 11 | 93025 | 15360 |
| 7,4 | 14 | 5527201 | 122880 |
| 9,3 | 12 | 461041 | 12288 |
| 9,4 | 16 | 42185025 | 196608 |
| 9,5 | 20 | 3477107089 | 3145728 |

These are exact shell-count identities from (PF7.1). They prove every
remaining endpoint and finish the \(D\ge3\) part of PF1.

### Squares: charge the two core selections before padding

Now \(a=(1,2)\), \(b=(n-1,n)\). Write \(k=4\) if \(n\equiv1\pmod4\)
and \(k=6\) otherwise. At the first cross-intersection, choose an entry
\(f\) and two disjoint \((k-1)\)-sets summing to \(f\); this consumes
\(2k-1\) entries. Then choose a disjoint analogous group based at \(g\)
for the other cross-intersection. It is sufficient that
\[
 \begin{split}
 R_{\mathrm{core}}&=n^2-2-(2k-1)>0,\\
 R_{\mathrm{core}}^2&>
       \begin{cases}15W,&k=4,\\40W,&k=6.\end{cases}   \tag{PF7.5}
 \end{split}
\]
The second selection is the more depleted one, so this pays for both.
Assign the two sets based at each crossing to its two incident
exceptional lines. Each line still needs \((n-k-1)/4\) zero four-sets.
There are \(n-k-1\) padding blocks in total. The final number of
nonexceptional entries used is \(4n-6\), so a convenient sufficient
condition for every padding selection is
\[
                   (n-2)^4>6W,                       \tag{PF7.6}
 \]
when padding is required. This uses the number left after *all* allocations
as a conservative lower bound before each selection. Every chosen entry
and cell is distinct; each nonexceptional line sum through an exception
is \(f+f=0\) or \(g+g=0\), plus the zero padding.

For \(n\ge47\) a single coarse invoice already proves both stages.
Put \(R_0=n^2-4n+2\); then (PF7.2) gives
\[
                  40W<320n^2\log_2n.
\]
Since \(R_0>n(n-4)\), it suffices that
\((n-4)^2>320\log_2n\). At 47 use
\(47^8<2^{45}\), so the right side is below 1800 while
\((47-4)^2=1849\). The difference is increasing for \(n\ge47\).
Also \(R_0\le R_{\mathrm{core}}\) and \(R_0<(n-2)^2\) in this range.

The exact finite invoice for every intervening odd order is:

| \(n\) | \(m\) | Strict core margin in (PF7.5) | Strict padding margin in (PF7.6) |
|---:|---:|---:|---:|
| 9 | 9 | 1344 | 865 |
| 11 | 9 | 1424 | 5025 |
| 13 | 10 | 17920 | 11569 |
| 15 | 10 | 24464 | 25489 |
| 17 | 11 | 63040 | 44481 |
| 19 | 11 | 80144 | 77377 |
| 21 | 12 | 155904 | 118033 |
| 23 | 12 | 184336 | 182193 |
| 25 | 12 | 348736 | 267553 |
| 27 | 12 | 430736 | 378337 |
| 29 | 13 | 630784 | 506865 |
| 31 | 13 | 734864 | 682705 |
| 33 | 13 | 1104960 | 898945 |
| 35 | 13 | 1305104 | 1161345 |
| 37 | 13 | 1788160 | 1476049 |
| 39 | 14 | 1946384 | 1825009 |
| 41 | 14 | 2672704 | 2264289 |
| 43 | 14 | 3043216 | 2776609 |
| 45 | 14 | 3941376 | 3369649 |

All margins are positive integers from (PF7.1), (PF7.5), and (PF7.6).
Together with the tail this proves the square part of PF1.

Finally fill all cells outside the two stars with the remaining exact
prescribed entries. The guaranteed sums are \(X\) and \(X+1\), respectively.
This completes the proof of PF1.

## 8. Why the new quadratic estimates do not prove full fixed-field arrays

**Proposition PF2 (conditional obstruction).** For odd \(n\ge3,D\ge2\),
put \(N=n^D\). In a uniform \(n\)-subset of the canonical binary pool,
\[
 \Pr(\text{bad sum}\mid X\text{ included})
                         \ge1-\frac1{N-1}.           \tag{PF8.1}
\]
The same holds for \(X+1\).

**Proof.** A successful subset containing \(X\) must omit \(X+1\) and
its other \(r=n-1\) entries must XOR to zero; this follows from evaluating
at 0 and 1, retaining the allowed irreducible sum \(X\).
Among the \(N-2\) nonexceptional entries, each \((r-1)\)-subset determines
at most one missing entry that completes its XOR to zero. Every successful
\(r\)-subset has \(r\) such deletions. Its number is therefore at most
\(\binom{N-2}{r-1}/r\). Divide by the full conditional sample count
\(\binom{N-1}{r}\) to obtain the success bound \(1/(N-1)\).
\(\square\)

Thus the small-bad-event input required by PL is impossible for this
unconstrained law. Improving its Fourier constants cannot fix this
quantitative obstruction. PF1 instead handles precisely these forced
lines by explicit additive construction; a theorem completing all
remaining lines is still missing.

The square construction's scalar order and nearby-prime target tables
also have no automatic finite-field analogue. The source's fixed-field
fresh-pair lemma CS-G supplies, for almost every allowed gap, many pairs
from a complete contained shell. But differences of degree-\(r\) monic
polynomials have degree less than \(r\). For irreducible endpoints of
degree \(r\ge2\) in characteristic two, they additionally vanish at 0 and 1.
Any gadget using only such differences
therefore preserves each affected line's high coefficients and its two
evaluation residues. Targets outside that image cannot be reached by
these gadgets. This is an exact image restriction, not a numerical
shortage that a smaller square cutoff removes.

Odd prime fields retain their own degree-drop and residue possibilities.
No statement here treats the characteristic as growing, replaces the
prescribed prefix by a complete top shell, or declares every order
divisible by the characteristic impossible. The source's explicit
degree-drop examples remain valid.

## 9. What transferred, verification, and remaining work

| Square improvement principle | Proved polynomial use here | Boundary |
|---|---|---|
| Work around the actual unused mean | Sharper actual lower-coefficient means and a leading mean at least \(2H/5\) | No scalar ordered central-stock construction over a finite field |
| Pay exact coupled finite inequalities | PQ-C proves every order in a full tail; PF1 pays each core/padding stage | Passing sampled endpoints alone would be insufficient |
| Exploit the target rather than a uniform worst case | Separate \(C=0\), small nonzero rational roots, and the actual leading window | Degree at least three needs a new reducibility argument |
| Use the actual admissible arithmetic image | Binary nonexceptional inputs lie in one codimension-two affine coset | Compatible full irreducible target vectors remain open |
| Preserve the exact prescribed pool during repair | Both arguments retain all inputs and the incomplete final shell | Thin Eisenstein lifts are different pools |

The main direct bottlenecks are now:

1. For primitive integer polynomial sums, impose content control while
   retaining a useful conditional sampling law. Equation (PQ6.2) rules
   out simply forgetting this requirement.
2. Over fixed \(\mathbb F_2\), complete all nonexceptional lines while
   preserving the now cheaper exact subsystem. Neither ambient
   irreducibility density nor a basis of fresh shell gaps supplies that
   completion theorem.
3. For further Q2 cutoff reductions, sharpen conditional anti-concentration
   near the rational-root locus or construct a more favorable distribution.
   The square's remaining numerical budget is the nonzero-root term.
   There is no demonstrated efficient constructor at any of the enormous
   Q2 bounds.

Run the exact controls from the PR86 repository root:

    python -B problems/prime-array-consolidation/code/polynomial_bound_transfer.py q2
    python -B problems/prime-array-consolidation/code/polynomial_bound_transfer.py f2 --order 5 --dimension 3
    python -B problems/prime-array-consolidation/code/polynomial_bound_transfer.py f2 --order 9 --dimension 2
    python -B problems/prime-array-consolidation/code/polynomial_bound_transfer.py test

The program uses only the Python standard library. The theorem controls
use integers and rational numbers, including all logarithmic upper
constants and all six cutoff tests. Binary shell counts are computed from
the root-count recurrence (PF7.1), independently of the source program's
Mobius implementation. Small oracles enumerate all monic binary
polynomials through degree 9 by trial factors, all 28 and 10626 subsets
conditioned on \(X\) in the order-3 and order-5 square pools, and 214872
integer quadratics in three root-window cases using discriminants rather
than the proof's factor enumeration. The conditional successful counts
are 0 and 213; the nonzero-constant reducible counts are 106, 457, 1893.
Failed sufficient invoices at binary orders 5 and 7 are explicitly
retained as negative controls, not as false nonexistence conclusions.

This is conventional mathematical proof plus exact finite computation.
It is not a kernel verification or an external acceptance claim.
Authorship: /root/symmetry_counting. Independent mathematical review must
be recorded against the exact new scientific source before promotion.

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
