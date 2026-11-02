# Prime targets and residue routing for all signed cube lines

Public proof manuscript. See [review and provenance](../PROVENANCE.md#full-signed-line-cube) for source revisions, review scope, and verification limits.

## 1. Exact target problem and compatibility

Use coordinates $`[n]=\{0,\ldots,n-1\}`$, put $`\bar t=n-1-t`$, and write
$`\rho_+(t)=t`$, $`\rho_-(t)=\bar t`$. Here $`n`$ is odd. The prescribed entry
pool, its largest member, total, and natural line mean are



```math
A_n=\{p_2,\ldots,p_{n^3+1}\},\qquad X=p_{n^3+1},\qquad
 T=\sum_{p\in A_n}p,\qquad \mu=T/n^2.
```



For an axis $`d\in\{0,1,2\}`$, $`U_d`$ is the target array indexed by the
other two coordinates, in their natural order. For $`i\lt j`$ and the remaining
axis $`k`$, let



```math
L_{ij,\varepsilon}(s)
 =\{x:x_i=t,\ x_j=\rho_\varepsilon(t),\ x_k=s,\ t\in[n]\}.
```



Write $`F_{ij,\varepsilon}(s)`$ for its target. These are the six families
of $`n`$ slice diagonals. The four body lines are



```math
B_{\varepsilon,\eta}
 =\{(t,\rho_\varepsilon(t),\rho_\eta(t)):t\in[n]\},
 \qquad (\varepsilon,\eta)\in\{+,-\}^2,
```



with targets $`b_{\varepsilon,\eta}`$. Together with the $`3n^2`$ axis
lines these give precisely $`3n^2+6n+4`$ distinct full signed-coordinate
lines when $`n\ge3`$.

The axis targets must satisfy their pairwise plane-marginal identities
and have directional grand total $`T`$. In addition, for every $`i\lt j`$,
$`\varepsilon\in\{+,-\}`$, and remaining coordinate $`k`$, one must have



```math
\sum_{s=0}^{n-1}F_{ij,\varepsilon}(s)
 =\sum_{t=0}^{n-1}U_k(t,\rho_\varepsilon(t)).                 \qquad\text{(1)}
```



Both sides partition the same diagonal square into lines. Equation (1)
asks for equality of two sums; it does not ask that their common value be
prime. There is no analogous body-total equation. The separate
[signed incidence theorem](signed_incidence.md#full-signed-line-integer-image)
proves that, for odd $`n\ge11`$, the axis identities
and the six equations (1) are the entire integer-image compatibility
conditions. In particular, there is no unmentioned factor-two condition
on the body targets. Its integer-lifting conclusion is distinct from a
permutation of the prescribed pool.

## 2. Analytic imports, with their actual length and modulus conditions

We use the finite list lemma FL from
[the public finite target-list lemma](../explicit-targets.md),
not the earlier ternary completion interface. At center $`y\gt 0`$, write
$`\ell=\lceil\log_2 y\rceil\ge2`$. FL requires an even modulus
$`2\le g\le16\ell`$, a list of $`k`$ unit residues $`a_i\pmod g`$ with
$`\sum_i a_i\equiv ky\pmod g`$, and an integer total $`ky`$. Its remaining
hypotheses are



```math
k\ge54000\ell^{11},\qquad
 2^{20}\ell^{11}\le d\le y/4,                              \qquad\text{(2)}
```



and the following counts in every interval $`I\subset[y-d,y+d]`$ of
length at least $`d/500`$:



```math
\pi(I;g,a)\ge\frac{|I|}{4g\ell}
 \quad\text{for every unit }a\pmod g,                     \qquad\text{(3)}
```





```math
\pi(I;q,a)\ge\frac{|I|}{4q\ell^9}
 \quad\text{for }2\le q\le128\ell^2
 \text{ and every unit }a\pmod q.                         \qquad\text{(4)}
```



Its conclusion is a list of primes in the requested original classes,
within distance $`d`$ of $`y`$, and with exact sum $`ky`$. Repeated target
primes are permitted. FL proves this using a repeatable difference,
complete-sequence growth, residue lifting, and greedy balancing. It
does not invoke a theorem for a growing system of prime affine forms.

The asymptotic count used here is the consequence printed in Section 1.2,
page 3, of Thorner--Zaman,
[*Refinements to the prime number theorem for arithmetic progressions*,
arXiv:2108.10878v2, 21 September 2021](https://arxiv.org/pdf/2108.10878v2).
It follows from their Theorem 1.1, Remark 1.2, and equation (1.6): for
fixed $`A\ge1`$ and $`\epsilon\gt 0`$, uniformly for
$`q\le(\log x)^A`$, reduced classes, and
$`h\ge x^{7/12+\epsilon}(\log x)^A`$ with $`h\le x`$, the weighted prime
count in $`(x-h,x]`$ is asymptotic to $`h/\phi(q)`$. The threshold is
ineffective. We retain that limitation.

For clarity, fix throughout this manuscript



```math
\beta=\frac{71}{120},\qquad
 \frac7{12}\lt \beta\lt \frac35,
 \qquad d(y)=\frac14 y^\beta.                              \qquad\text{(5)}
```



For every sufficiently large $`y`$, every interval in
$`[y-d(y),y+d(y)]`$ of length at least $`d(y)/500`$, and every reduced
class modulo $`q\le128\lceil\log_2 y\rceil^2`$, the cited estimate gives



```math
\pi(I;q,a)\ge \frac{|I|}{2\phi(q)\log(2y)}.               \qquad\text{(6)}
```



Indeed take $`A=3`$ and
$`\epsilon=(\beta-7/12)/2=1/240`$. For the right endpoint $`x\sim y`$,
the lower bound $`|I|\ge y^\beta/2000`$ exceeds
$`x^{7/12+\epsilon}(\log x)^3`$ eventually; its positive power saving
dominates the logarithmic factor. Also
$`128\lceil\log_2 y\rceil^2\le(\log x)^3`$ eventually. Dividing the
weighted count by $`\log(2y)`$ yields (6). Endpoint conventions affect
at most one prime and do not affect the eventual lower bound.

Since $`\phi(q)\le q`$ and
$`\ell\sim\log y/\log2`$, equation (6) implies both (3) and (4).
Equations (2) follow once the length condition is checked, because
$`0\lt \beta\lt 1`$ and a positive power dominates every fixed power of the
logarithm. These checks remain uniform when $`y/\mu\to1`$ uniformly.

## 3. Complete prime-target theorem

The baseline symmetric target theorem CT in
[cube_targets.md](cube_targets.md) gives a symmetric $`n\times n`$ prime
matrix $`P`$ with



```math
\sum_{i,j}P_{ij}=T,\qquad |P_{ij}-\mu|\le\mu^{3/5},       \qquad\text{(7)}
```



in any prescribed symmetric unit-residue pattern modulo an even
$`g\le16\lceil\log_2 X\rceil`$ whose total is $`T\pmod g`$.
Existence is uniform over these moduli and patterns for all sufficiently
large odd $`n`$. Use this matrix as the directional target tensor in all
three orientations. Symmetry supplies every axis plane-marginal
identity, not merely equality of the three grand totals.

Put



```math
S_+=\sum_iP_{ii},\qquad S_-=\sum_iP_{i,\bar i},\qquad
 y_\varepsilon=S_\varepsilon/n.                           \qquad\text{(8)}
```



The two integers $`S_\varepsilon`$ are odd. Equation (7) gives



```math
|y_\varepsilon-\mu|\le\mu^{3/5}.                         \qquad\text{(9)}
```



**Theorem SPT (signed prime targets).** There is an ineffective
threshold $`n_0`$ such that for every odd $`n\ge n_0`$ and every even
$`2\le g\le16\lceil\log_2 X\rceil`$ there is a prime target for each
full signed-coordinate line satisfying all exact compatibility equations
and with every target at distance at most $`2\mu^{3/5}`$ from $`\mu`$.
Every target is a unit modulo $`g`$. Repetitions of target values are
allowed.

More precisely, after choosing any symmetric axis residue matrix of
total $`T\pmod g`$, choose $`P`$ as above. For each of the six face
families, prescribe **any** unit residue list of length $`n`$ with sum
$`S_\varepsilon\pmod g`$. Prescribe the four body residues as arbitrary
units modulo $`g`$. All these prescriptions can be met simultaneously.

**Proof.** The prime number theorem and partial summation give



```math
X\sim3n^3\log n,\qquad T\sim\frac32 n^6\log n,
 \qquad \mu\sim\frac32 n^4\log n.                         \qquad\text{(10)}
```



The baseline CT applies uniformly for the displayed moduli. For either
center $`y=y_\varepsilon`$, equation (9) gives $`y/\mu\to1`$ uniformly.
Consequently



```math
\frac{\lceil\log_2 X\rceil}{\log_2 y}\longrightarrow\frac34.
```



Thus $`g\le16\lceil\log_2 y\rceil`$ with fixed logarithmic slack for
all sufficiently large $`n`$, even when the allowed modulus is as large
as its displayed bound. Moreover
$`n/(\lceil\log_2 y\rceil)^{11}\to\infty`$, uniformly in the two
centers and all choices of $`P`$ satisfying (7). This proves the actual
length requirement in (2), with $`k=n`$.

Apply FL separately to every face family at center
$`y_\varepsilon`$, radius $`d(y_\varepsilon)`$, integer total
$`S_\varepsilon`$, and the prescribed unit residue list. The exact
congruence requirement is part of the list prescription; (2)--(4)
hold by the preceding checks. Each resulting list sums to
$`S_\varepsilon`$ exactly. Since the same $`P`$ is used in all orientations,
this is exactly equation (1) for that family.

Every face target $`f`$ satisfies



```math
|f-\mu|
 \le \mu^{3/5}+\tfrac14y_\varepsilon^\beta
 \le2\mu^{3/5}                                             \qquad\text{(11)}
```



eventually, uniformly, because $`\beta\lt 3/5`$ and
$`y_\varepsilon\sim\mu`$. For each body class, equation (6), applied
at center $`\mu`$, supplies a prime within $`d(\mu)`$ of $`\mu`$ in that
class. There are only four body targets, with no prescribed total or
relation to one another. The separate incidence theorem says these
choices impose no further integer compatibility conditions once
$`n\ge11`$.

The targets satisfy all required identities, their grand total is the
fixed $`T`$ in each axis direction, and the claimed radius follows from
(7) and (11). All thresholds depend on fixed numerical constants and
the pinned analytic import, not on the modulus, residue patterns, or
order within the odd tail. QED.

The extension step does not require symmetry once the axis targets have
been supplied. More generally, take any compatible prime axis target
triple, in unit classes modulo the same $`g`$, whose entries differ from
$`\mu`$ by at most $`\mu^{3/5}`$. Use the six right sides of (1) separately
as the face totals. Each is odd and its quotient by $`n`$ satisfies (9),
so exactly the same six FL applications and four body choices extend
that given triple. Symmetry is the proved device for constructing an
initial axis triple with the exact pool total; it is not an additional
incidence identity imposed on the face or body targets.

At the entry-pool scale this radius is small:



```math
\frac{2\mu^{3/5}}X
 \asymp n^{-3/5}(\log n)^{-2/5}\longrightarrow0.             \qquad\text{(12)}
```



In particular it is $`o(KX)`$ for every controller scale $`K\to\infty`$.
After the axis construction there are six finite prime-list uses and
four independent single-coordinate prime choices. They can also be
reduced to two shared face lists and one
shared body value when no individual residue prescriptions are needed.
No prime-pattern theorem with complexity growing with $`n`$ has been
assumed.

### Unit residues always exist for the requested face totals

For an even modulus $`g`$, every odd residue is a sum of three units.
At each odd prime divisor $`p`$ of $`g`$, set the first unit to 1 and
choose the second residue different from 0 and from the value making
the third zero. At most two residues are excluded, so a choice exists
even at $`p=3`$. At the power of 2, choose the second residue odd;
the third is then odd. Choose lifts to each prime power and apply CRT.

For odd $`n\ge3`$ and odd $`S`$, fix the first $`n-3`$ units to 1 and apply
this construction to the remaining odd residue. Hence every family in
(8) has an admissible length-$`n`$ residue list. These lists are selected
after $`P`$ is fixed; imposing unit residues on the common section total
would be an unnecessary restriction. The total $`S`$ itself need not be
a unit modulo $`g`$ or a prime.

The same construction supplies the baseline symmetric axis residue
matrix, by setting every entry to 1 except three diagonal entries. Thus SPT is
an existence theorem, not merely an implication from an unverified
residue prescription.

## 4. Residue-routing interface for the physical controller

This section isolates the finite modular routing used after the axis
residues have been corrected. It is an algebraic consumption lemma;
the separate physical construction must supply the disjoint prime-entry
gadgets and their placement.

Let $`g=2h`$. Fix any compatible vector of odd integer signed-line targets;
these need not be prime or units modulo $`g`$. Suppose an arrangement of
odd entries has axis sums congruent modulo $`g`$ to those axis targets.
Suppose that available
disjoint switches have these exact signed-line actions:

1. For each of the four body lines, a switch preserves every axis sum,
   changes that body sum by an actual difference $`d\equiv2\pmod g`$,
   and preserves the other three body sums. Its changes to face lines
   may be nonzero; every face-family total is preserved because the
   axis sums are preserved.
2. For each face family and each adjacent pair of its fixed-coordinate
   levels, a switch preserves all axes, all bodies, and every other
   face family, and changes the two selected face sums by $`+d,-d`$,
   where $`d\equiv2\pmod g`$.

The separate incidence construction uses axis-neutral alternating
eight-cell cuboids with unit coefficient on their native body or face
transfer. Actual switches use four distinct equal-gap prime pairs.
The coefficient is one, not two: using identical two-coordinate sets
in a face cuboid would create an avoidable factor-two restriction.

**Lemma SR (bounded modular routing).** If $`h-1`$ disjoint switches of
each type above are available, all signed-line residues can be made
equal to the prescribed odd target residues, preserving the already
correct axis residues. In particular this applies to every SPT vector.
At most



```math
[4+6(n-1)](h-1)=(6n-2)(h-1)                              \qquad\text{(13)}
```



switches are used. Thus eight-cell implementations consume at most
$`8(6n-2)(h-1)`$ cells. This is an addition of $`O(ng)`$ cells to the
separate axis residue mechanism.

**Proof.** Every current and desired line sum is odd, so divide their
difference by 2 and work modulo $`h`$. Each body switch has native
increment 1 in this quotient. Use between 0 and $`h-1`$ switches to set
each body residue, leaving the other bodies and the axes unchanged.

Now fix a face family. Its desired total is the matching aggregate of
axis targets. Its current total is the same aggregate of the current
axis sums. These are congruent modulo $`g`$; consequently the quotient
errors $`e_s=(F(s)-\text{current}(s))/2\pmod h`$ have sum zero.
For the path generators $`\mathbf e_s-\mathbf e_{s+1}`$, take



```math
c_s=\sum_{t=0}^s e_t\pmod h,\qquad 0\le s\lt n-1,
```



represented by integers in $`\{0,\ldots,h-1\}`$. Their incidence image
is exactly the error vector modulo $`h`$. Use $`c_s`$ switches on edge
$`s`$. These operations preserve the bodies and all other face families,
so all six paths can be processed independently. If $`h=1`$, every
residue was already correct and no switch is needed. Counting the
available types gives (13). QED.

This argument does not select equal-gap pairs from the pool, prove they
survive prior allocations, bound nonnative line loads, or pay their
integer side effects. Those are physical-controller obligations. It
does establish that target primes impose no additional modular demand
beyond the displayed unit cuboids and the baseline axis residue repair.
In particular, a gcd computation without these coefficient-one actions
would not suffice.

[Back to the four-manuscript index](../README.md).
