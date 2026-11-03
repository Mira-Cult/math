**Public reading copy.** Presentation and links have been normalized. Historical status statements below belong to their source revisions; see the [current publication status](../../README.md#review-and-verification-status). The matching original bytes are in the [source archive](../../originals/manuscripts/hyperk_targets.md).

# Joint prime targets in every fixed dimension

Author: `/root/targets`. Manuscript-local labels only; no permanent claim IDs
are allocated. This manuscript extends the reviewed four-dimensional target
source at `b837e307fc41975d0fb332c8215d6835ba47a271`, delivered in
`112c2bca0d38f82391a34994b63153e7ec08aa74`, without modifying that source.
The absolute-label-set prescription is inherited from
[hyper4_targets.md](hyper4_targets.md). The dimension-parametric weights,
their exact gcd, and the two-list completion below are new here.

The unconditional result of this manuscript is a prime target vector satisfying
**every signed two-block partition identity**, with the exact axis total and
a uniform short window. Membership in the full integer incidence image uses
the separate incidence theorem; a prescribed-pool permutation uses the
separate physical controller. Neither is inferred from target construction.

## 1. Target prescription and compatibility

Fix an integer `k>=2`, put `r=k-1`, and let `n=2m+1>=3`. Set


```math
I=\{-m,\ldots,m\},\qquad J=\{0,\ldots,m\}.
```


A full signed-coordinate line is described by a nonempty varying block
`A subset [k]`, signs `sigma_i` on that block, and fixed coordinates
`c_j in I` outside it. Identify simultaneous sign reversal. For every
nonempty ordinary set `S subset J` with `|S|<=r`, choose an integer `q_S`.
Repeated labels are forgotten, and define `q_empty=q_{ {0} }`. Prescribe


```math
y(A,\sigma,c)=q_{\{|c_j|:j\notin A\}}.                 \qquad\text{(K1)}
```


**Lemma KP.** For arbitrary integer choices of the `q_S`, (K1) satisfies
every signed two-block partition identity. In particular all axis-direction
grand totals agree.

**Proof.** Let `A,B` be disjoint nonempty varying blocks with signs `sigma,tau`,
and fix `c` outside their union. Put `S={|c_j|:j notin A union B}`. The term
with parameter `u` in the sum of the `A`-line targets over the `B` parameter
is `q_{S union {|u|}}`. The term with parameter `t=u` in the reverse partition
sum is precisely the same integer. This proves equality term by term, for
every sign pattern, block size and fixed-coordinate placement. The case
`S=empty` uses singleton labels and is included. Body targets never occur
inside a two-nonempty-block identity; the chosen empty-set convention is
harmless. The axis tensors are identical symmetric tensors, so their grand
totals agree as well. QED.

This verifies all such identities, including traces of complementary blocks.
It does not presume that those are the full integer-image conditions.

## 2. Exact weights in the axis total

The common axis tensor is `q_{ {|x_1|,...,|x_r|} }` on `I^r`. For a set
with `s>=1` nonzero labels and no zero, its weight is


```math
w_{r,s}=2^r\sum_{j=0}^s(-1)^{s-j}\binom{s}{j}j^r
        =2^r s!\,{r\brace s},\qquad 1\le s\le r.        \qquad\text{(K2)}
```


Here the final equality can be read as the definition of the number of
surjections divided by `s!`; the inclusion-exclusion expression is primary.
There are `binom(m,s)` such sets. For a set containing zero and exactly
`s` nonzero labels, its weight is


```math
v_{r,s}=\sum_{j=0}^s(-1)^{s-j}\binom{s}{j}
                   \big((1+2j)^r-(2j)^r\big),
       \qquad 0\le s\le r-1.                           \qquad\text{(K3)}
```


There are again `binom(m,s)` such sets. The center has weight `v_{r,0}=1`.
Formulas (K2)--(K3) count ordered signed tuples using every selected label:
each nonzero occurrence has two signs and each zero occurrence has one.
For (K3), subtraction first requires zero to occur, and inclusion-exclusion
then requires every nonzero label. These classes partition `I^r`; hence


```math
\sum_{s=1}^r\binom ms w_{r,s}
 +\sum_{s=0}^{r-1}\binom ms v_{r,s}=(2m+1)^r.           \qquad\text{(K4)}
```


As usual `binom(m,s)=0` if `s>m`. Every weight is at most


```math
W_r=(2r)^r.                  \qquad\text{(K5)}
```


Indeed at most `r` labels occur, and their total number of signed representatives
is at most `2r`. All constants in this manuscript may depend on fixed `r`.

The two reserve classes used below have `m` variables each and weights


```math
a_r=w_{r,1}=2^r,\qquad
 b_r=v_{r,1}=3^r-2^r-1\quad(r\ge2).                    \qquad\text{(K6)}
```


The second class does not exist at `r=1`; that case has only weight-2
nonzero singletons and the weight-1 center.

| `k` | `r` | `a_r` | `b_r` | gcd of all noncentral weights | center modulus used below |
|---:|---:|---:|---:|---:|---:|
| 2 | 1 | 2 | absent | 2 | 4 |
| 3 | 2 | 4 | 4 | 4 | 8 |
| 4 | 3 | 8 | 18 | 2 | 4 |
| 5 | 4 | 16 | 64 | 16 | 32 |
| 6 | 5 | 32 | 210 | 2 | 4 |

Thus the four-dimensional weights 8 and 18 are not reused unchanged.
In dimension five the reserve gcd is 16, a substantive congruence.

## 3. The reserve gcd is always a power of two

Write `nu_2(r)` for the exponent of 2 dividing a positive integer `r`.

**Lemma KG.** For `r>=2` and `m>=1`, the gcd of all noncentral weights
present in (K4) is `D_r=gcd(a_r,b_r)`, where


```math
D_r=\begin{cases}
 2,&r\text{ odd},\\
 2^{\min(r,\nu_2(r)+2)},&r\text{ even}.
 \end{cases}                                           \qquad\text{(K7)}
```


For `r=1` put `D_1=2`. In particular `2D_r` is a power of two.

**Proof.** Since `a_r=2^r`, the gcd with `b_r` is a power of two.
For odd `r>=3`, `b_r=3^r-2^r-1=2 mod 4`, proving (K7).
For even `r=2^u v` with `v` odd, `u>=1`,


```math
\nu_2(3^r-1)=u+2.
```


To verify this elementary valuation, start with `3^2-1=8`. Each subsequent
squaring multiplies by `3^{2^j}+1`, which is `2 mod 8` for `j>=1`, and
so adds exactly one to the valuation. Multiplication of the exponent by
the odd number `v` adds the odd geometric sum and changes no valuation.
Subtracting `2^r` gives the asserted gcd with `2^r`, including the cases
`u+2>=r`, where both terms are divisible by `2^r`.

It remains to show that every other weight is divisible by `D_r`.
The weights (K2) are all divisible by `2^r`. For odd `r`, (K3) is even
when `s>=1`: each parenthesis is odd, and its alternating coefficient
sum is zero. For even `r`, every odd integer `z` satisfies
`z^r=1 mod 2^{u+2}`. This follows from `z^2=1 mod 8` and repeated
squaring, then raising to the odd power `v`. Consequently


```math
(1+2j)^r-(2j)^r=1\pmod{D_r}
```


for every integer `j`, because `D_r` divides `2^r`. In (K3) with
`s>=1`, the alternating sum of those constant residues is zero. Thus all
noncentral weights are divisible by `D_r`. Conversely the two present
singleton classes have gcd `D_r`, proving the claim. QED.

The fact that the gcd is a power of two matters analytically: any odd
residue modulo `2D_r` is a reduced class and may contain a prime center.
There is no need to force a large center prime into a nonunit odd-prime class.

## 4. One-dimensional prime inputs

We use exactly the finite list lemma **FL** in
[PR77's explicit_prime_targets.md at
`c2118dfad1aeb660d66308dc6a94d6c959f5010c`](explicit_prime_targets.md).
Its source SHA-256 is
`0e6ff5f0c26c6a2a6e66d0ae2b1a2ef581f282662a8e772e827ba04fd72f45e1`.
For completeness, at a center `y>0` and `ell=ceil(log_2 y)>=2`, FL takes
an even original modulus `2<=g<=16ell`, a list of unit classes `a_i`,
an integer desired total `hy` with `sum a_i=hy mod g`, and radius `delta`.
It requires


```math
h\ge54000\ell^{11},\qquad
 2^{20}\ell^{11}\le\delta\le y/4.                       \qquad\text{(K8)}
```


Every interval inside `[y-delta,y+delta]` of length at least `delta/500`
must contain at least `|I|/(4g ell)` primes in each reduced class modulo
`g`, and at least `|I|/(4q ell^9)` in each reduced class for **every**
`2<=q<=128ell^2`. The conclusion is a length-`h` list of primes in the
specified classes, with exact sum `hy` and distance at most `delta` from
`y`. Repetitions are permitted. Every application below uses `g=2` and
all original classes 1. The lists have length `m`, not `n`.

The prime-counting input is Thorner--Zaman,
[*Refinements to the prime number theorem for arithmetic progressions*,
arXiv:2108.10878v2, 21 September 2021](https://arxiv.org/pdf/2108.10878v2),
Theorem 1.1, Remark 1.2, equation (1.6), and the explicit short-interval
consequence in Section 1.2, printed page 3. For fixed `A>=1` and `epsilon>0`,
it gives the weighted prime asymptotic `h/phi(q)` uniformly in reduced
classes for `q<=(log x)^A` and
`x^(7/12+epsilon)(log x)^A<=h<=x`. Its threshold is ineffective.
In particular the possible exceptional zero has not been excluded.

Set


```math
\beta=71/120,\quad \delta=\mu^\beta/4,\quad
 \epsilon=1/240,\quad A=3.                              \qquad\text{(K9)}
```


The local consequence TC, proved in
[cube_targets.md](cube_targets.md#uniform-local-counting-consequence), gives
for every interval inside `[mu-2delta,mu+2delta]` of length at least
`delta/500` and every reduced class modulo
`2<=q<=128(ceil(log_2 mu)+1)^2`,


```math
\pi(I;q,a)\ge
              \frac{|I|}{2\varphi(q)\log(2\mu)}.        \qquad\text{(K10)}
```


The source's power slack is `beta-7/12-epsilon=1/240>0`; it absorbs the
fixed interval factor and the cubic logarithm. A fixed modulus `2D_r`
also lies in this range once `mu` is sufficiently large depending on `r`.
No prime-pattern theorem whose number of forms grows with `m` is used.

## 5. Uniform weighted exact completion

**Theorem KW.** For every fixed integer `r>=1` there is an ineffective
constant `M_r` such that the following holds. Let `n=2m+1`, `T` be odd,
and `mu=T/n^r`. Assume


```math
\mu\ge M_r,\qquad
 m\ge60000(\lceil\log_2\mu\rceil+1)^{11}.              \qquad\text{(K11)}
```


Then one can choose a prime `q_S` for every nonempty `S subset {0,...,m}`
with `|S|<=r` so that its weighted axis sum is exactly `T` and


```math
|q_S-\mu|\le\mu^{3/5}.        \qquad\text{(K12)}
```


Every threshold is uniform in `m,T` subject to (K11); `r` is fixed first.

**Proof for `r>=2`.** Abbreviate `a=a_r`, `b=b_r`, `D=D_r`, `W=W_r`,
and use `delta` in (K9). Reserve the center, all `m` singleton variables
`q_{ {j} }`, and all `m` doubleton variables `q_{ {0,j} }`, for `1<=j<=m`.
Every remaining variable is called bulk. Equation (K10) gives an odd prime
in `[mu-delta,mu-delta/2]` and one in `[mu+delta/2,mu+delta]`.
Process the bulk variables in any fixed order. For a variable of weight
`w<=W`, choose the lower prime when the current weighted discrepancy is
nonnegative, and the upper prime when it is negative. Each increment has
opposite weak sign and magnitude at most `W delta`. Induction gives


```math
B=W_{\rm bulk}\mu+E,\qquad |E|\le W\delta,             \qquad\text{(K13)}
```


where `B` is the actual integer bulk sum. This bound is independent of
the growing number of variables. Repeating prime targets here does not
reuse any entry of the prescribed pool.

Choose a prime center `q_0=q_{ {0} }` in `[mu-delta,mu+delta]` with


```math
q_0\equiv T-B-(a+b)m\pmod{2D}.        \qquad\text{(K14)}
```


The residue is odd because `T` is odd and all noncentral weights are even.
By Lemma KG the modulus is a power of two, so the residue is a unit.
Equation (K10) supplies this prime, uniformly in the residue. Put


```math
R=T-B-q_0=(a+b)m\mu-\varepsilon,\quad
 |\varepsilon|\le(W+1)\delta,
 \quad R\equiv(a+b)m\pmod{2D}.                          \qquad\text{(K15)}
```


We now solve `a S_a+b S_b=R` with `S_a=S_b=m mod 2` and both totals
close to `m mu`; this step is integral, not rational elimination.
Put `A=a/D`, `B'=b/D`, so `gcd(A,B')=1`, and set


```math
H=\frac{R-(a+b)m}{2D}\in\mathbb Z.
```


If `A>1`, choose `v` in the unique residue class
`B' v=H mod A` nearest to `(m mu-m)/2`; if `A=1`, choose the nearest
integer with no residue restriction. In both cases set


```math
S_b=m+2v,\qquad
 S_a=\frac{R-bS_b}{a}.                                 \qquad\text{(K16)}
```


The congruence makes `S_a=m+2u` for an integer `u`. Thus both totals
are integers with parity `m`, their weighted sum is exactly `R`, and


```math
\eta=S_b-m\mu,\quad |\eta|\le A,\qquad
 |S_a-m\mu|\le\frac{W+1}{a}\delta+\frac bD.              \qquad\text{(K17)}
```


There is no inverse modulo `A` to take when `A=1`; this includes
`r=2,4`. Formula (K17) follows by expanding (K15) in (K16).

To make all eventual constants explicit at this algebraic stage, it is
enough that `delta>=1` and


```math
m\ge C_r:=8(W_r+a_r+b_r+1).          \qquad\text{(K18)}
```


Indeed `A<=a`, so (K17) then yields
`|S_a/m-mu|<=delta/4` and `|S_b/m-mu|<=delta/4` with ample margin.
Enlarge `M_r` so that (K11) implies (K18), `delta>=1`, and (K10)
holds including `q=2D_r`. Write `y_a=S_a/m` and `y_b=S_b/m`.

Apply FL twice, at these two centers, with radius `delta`, length `m`,
original modulus 2, and all requested classes 1. The exact totals and
parities were proved in (K16). For each actual center `y_i`,
`ell_i=ceil(log_2 y_i)<=ceil(log_2 mu)+1` eventually, so (K11) implies
the required `m>=54000ell_i^11`. The inequalities
`2^20ell_i^11<=delta<=y_i/4` follow uniformly from `0<beta<1`.
Every required interval lies inside `[mu-2delta,mu+2delta]` and has length
at least `delta/500`; every auxiliary modulus up to `128ell_i^2` is in
(K10). Finally, uniformly at these centers,


```math
2\varphi(q)\log(2\mu)\le4q\ell_i
                              \le4q\ell_i^9
```


eventually. Thus (K10) implies both the strong original-modulus count and
the weak full auxiliary-modulus count in FL. This verifies all its hypotheses.

Assign the two lists to the two reserve classes. Their weighted total is
`R`, so the full total is `T`. The finishing primes have distance at most
`5delta/4` from `mu`; the others have distance at most `delta`. Since
`beta<3/5`, these bounds imply (K12) for sufficiently large `mu`.

**The case `r=1`.** There are only the center and the `m` variables of weight
2. Choose `q_0=T-2m mod 4` in `[mu-delta,mu+delta]`. This is an odd/unit
class. Then `S=(T-q_0)/2` is an integer of parity `m`, and
`|S/m-mu|<=delta/(2m)`. One application of FL with length `m`, modulus 2,
radius `delta`, and center `S/m` finishes exactly as above. The body
diagonal targets can still use `q_0`. This proves the theorem for every
fixed `r>=1`. QED.

The center congruence is necessary for this two-list architecture. Once
all finishing primes are odd, their weighted sum is `(a+b)m mod 2D`.
An arbitrary odd prime center can leave the wrong class. Matching only
modulo `D`, or only imposing oddness, is insufficient when `D>1`.

## 6. The prescribed first-prime pool

**Theorem KPT.** For every fixed integer `k>=2`, there is an ineffective
integer `N_T(k)` such that for every odd `n>=N_T(k)`, the pool


```math
P=\{p_2,\ldots,p_{n^k+1}\},\quad
 X=p_{n^k+1},\quad T=\sum_{p\in P}p,\quad
 \mu=T/n^{k-1}
```


admits a prime target on every full signed-coordinate line satisfying:

1. Every signed two-block partition identity holds exactly.
2. Every axis-direction grand total equals the exact pool total `T`.
3. All targets are odd primes within `mu^(3/5)` of `mu`.
4. A single vector is reduced modulo every even
   `2<=g<=16ceil(log_2 X)` simultaneously.

Repeated line targets are allowed. The construction is (K1); the empty-set
target is the center prime. This theorem alone asserts no integer-array lift
and no placement of the entries of `P`.

**Proof.** The prime number theorem and partial summation give, for fixed `k`,


```math
X\sim k n^k\log n,\quad
 T\sim\frac{k}{2}n^{2k}\log n,\quad
 \mu\sim\frac{k}{2}n^{k+1}\log n.                       \qquad\text{(K19)}
```


The exact total is odd, because it sums an odd number of odd primes.
Thus `mu` tends to infinity and `m/(ceil(log_2 mu)+1)^11` tends to infinity
along the entire odd tail. KW applies with `r=k-1`; KP and the weight
identity (K4) supply the partition equations and exact total. Eventually
every target exceeds `16ceil(log_2 X)`, so a target prime divides none of
the allowed moduli, proving the simultaneous unit assertion. QED.

The target error satisfies


```math
\frac{\mu^{3/5}}{X}
 \sim\frac{(k/2)^{3/5}}{k}\,
 n^{(3-2k)/5}(\log n)^{-2/5}\longrightarrow0             \qquad\text{(K20)}
```


for every fixed `k>=2`. Thus it is `o(X)`, and in particular `o(K_0 X)`
for the controller baseline `K_0=n^(3/5)`. Neither the argument nor its
threshold is uniform for dimensions growing with `n`.

If a separate theorem proves that the partition equations characterize
the integer image at sufficiently large odd `n`, KPT has an odd integer
lift: the integral vector `(y-n)/2` satisfies the same homogeneous equations,
so lift it to an integer array `z` and use `1+2z`. Its total is `T` by an
axis partition. This conditional consequence must not be confused with a
permutation of `P`.

## 7. Architectures and finite controls

Independent prime choices per line do not preserve overlapping section
partitions. Extending an arbitrary axis target tensor by separately choosing
prime lists on the other families leaves coupled trace conditions unresolved.
The set prescription (K1) imposes those identities before prime selection.
Its residual analytic problem is one bounded-weight equation, solved above
with one center and at most two finishing lists. The gcd computation shows
why merely repeating the four-dimensional weights or center modulus fails.

The executable [hyperk_targets.py](../../originals/code/hyperk_targets.py) independently
counts tuple weights, tests (K7) against all weight classes, checks exact
centered integer completion including `A=1`, generates full signed line sets
by two methods, and checks all two-block partition identities. Finite prime
target certificates check primality and the exact first-pool total separately.
Their finite search is not an implementation of FL's asymptotic proof.
No target certificate is an arrangement certificate or evidence that an
unproved integer saturation statement holds.

Run from the repository root:

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyperk_targets.py self-test
```

The exact commands and retained input descriptions are recorded with the
eventual frozen source/review revision in the general-dimension handoff.
The manuscript's mathematical proofs are conventional, not kernel checked.
