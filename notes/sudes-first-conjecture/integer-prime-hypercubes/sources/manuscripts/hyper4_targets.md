**Public reading copy.** Presentation and links have been normalized. Historical status statements below belong to their source revisions; see the [current publication status](../../README.md#review-and-verification-status). The matching original bytes are in the [source archive](../../originals/manuscripts/hyper4_targets.md).

# Compatible prime targets for all signed lines in four dimensions

Author: `/root/hyper_targets`. The absolute-coordinate-set construction in
Section 2 was proposed by `/root/hyper_incidence`; that agent is a coauthor
of this construction and cannot supply its independent mathematical review.
All labels below are manuscript-local. No inherited claim or hypothesis is
changed. This source extends the targets at PR79 scientific revision
`a2445962ec6e06b2a893980fb7a183057eb9bcee`, delivery
`cdb7879e358f93afa54b685027a27692d22635a9`.

The proved obligation is **existence of a compatible prime target vector**.
The separate four-dimensional physical controller must realize this vector
by a permutation of the prescribed pool. An integer lift, even an odd
integer lift, is not such a permutation. Independent review of this new
manuscript is pending.

## 1. Exact geometry and the target interface

Let `n=2m+1` be odd and write centered coordinates


```math
I=\{-m,\ldots,m\},\qquad J=\{0,\ldots,m\}.
```


Translation identifies `I` with the user's `[n]`. A full signed line is
specified by a nonempty set of varying coordinates
`A subset {1,2,3,4}`, signs `sigma_i in {+1,-1}` for `i in A`, and fixed
coordinates `c_j in I` for `j notin A`:


```math
L(A,\sigma,c)=\{x:x_i=\sigma_i t\ (i\in A),\quad
                    x_j=c_j\ (j\notin A),\ t\in I\}.
                                                        \qquad\text{(HT1)}
```


Fix the first sign to `+1` to quotient simultaneous reversal. For `n>=3`
the resulting distinct line count is


```math
\sum_{a=1}^4\binom4a2^{a-1}n^{4-a}
 =4n^3+12n^2+16n+8.                                      \qquad\text{(HT2)}
```


Let `y(A,sigma,c)` denote a line target. For disjoint nonempty coordinate
blocks `A,B`, sign patterns `sigma,tau`, and fixed coordinates `c` on
the complement `C`, the two partitions of the same signed two-parameter
section give the necessary identity


```math
\sum_{u\in I}y(A,\sigma,(\tau u,c))
 =\sum_{t\in I}y(B,\tau,(\sigma t,c)).                    \qquad\text{(HT3)}
```


The possible block sizes are `(1,1)`, `(1,2)`, `(1,3)`, and `(2,2)`,
up to exchanging the blocks. Thus (HT3) includes the axis marginals;
both margins of each of the twelve two-coordinate-family matrices;
the totals of the sixteen three-coordinate-family vectors; and all
cross-trace identities between complementary two-coordinate families.
It is stronger than matching the four axis grand totals.

The separate eventual signed-incidence theorem SI4 in
[hyper4_incidence.md](hyper4_incidence.md) proves that for odd `n>=17`
these partition identities are the full integer-image conditions. In
particular their image lattice is saturated, and an odd target vector
satisfying them has an odd integer lift. The argument below checks
(HT3) directly, without independently prescribing overlapping lists.
No section sum is required to be prime.

For the prescribed pool put


```math
P_n=\{p_2,\ldots,p_{n^4+1}\},\qquad X=p_{n^4+1},\qquad
 T=\sum_{p\in P_n}p,\qquad \mu=T/n^3.                    \qquad\text{(HT4)}
```


Its total `T` is odd. A valid target vector must have axis grand total
`T` in each of the four orientations. The axis controller and the
axis-neutral signed-line controller receive the same vector; this
source does not select independent incompatible targets for their stages.

## 2. One structured prescription checks every partition identity

For every nonempty **ordinary set** `S subset J` of at most three labels,
choose a prime `q_S`. Repeated labels are forgotten. Set
`q_empty=q_{ {0} }` for use on the eight full diagonals, and prescribe


```math
y(A,\sigma,c)=q_{\{|c_j|:j\notin A\}}.                  \qquad\text{(HT5)}
```


In particular the four directional axis tensors are copies of


```math
P(x,y,z)=q_{\{|x|,|y|,|z|\}},                           \qquad\text{(HT6)}
```


the twelve pair-family matrices are copies of
`Q(z,w)=q_{ {|z|,|w|} }`, the sixteen triple-family vectors are copies
of `R(w)=q_{ {|w|} }`, and all eight full-diagonal targets are `q_{ {0} }`.
Signs and coordinate orientations do not affect these values.

**Lemma HP (partition compatibility).** Every vector (HT5), with
arbitrary integer values `q_S`, satisfies (HT3).

**Proof.** Let `S_C={|c_j|:j in C}`. The summand indexed by `u` on
the left of (HT3) is exactly


```math
q_{S_C\cup\{|u|\}}.
```


The summand indexed by `t=u` on the right is the same number. Absolute
values remove the signs and taking an ordinary set removes repetitions
coming from the several coordinates in one varying block. This proves
term-by-term equality for every disjoint block pair, including `(2,2)`.
The argument never treats different overlapping family prescriptions as
independent. QED.

For example `P(t,sigma*t,w)=Q(t,w)` gives the pair-family margins;
`Q(t,sigma*t)=R(t)` makes all complementary cross traces agree; and
`P(t,sigma*t,tau*t)=R(t)` gives each triple-family total. These are
checks of sums, not claims that their common sums are prime.

The exact axis total remains a single weighted equation. If `a,b,c`
are distinct nonzero labels, the weights with which each variable occurs
in (HT6) are as follows.

| Label set | Number of ordered signed triples | Number of these sets |
| --- | ---: | ---: |
| `{0}` | 1 | 1 |
| `{a}` | 8 | `m` |
| `{0,a}` | 18 | `m` |
| `{a,b}` | 48 | `binom(m,2)` |
| `{0,a,b}` | 24 | `binom(m,2)` |
| `{a,b,c}` | 48 | `binom(m,3)` |

For `{0,a}`, the count is `3^3-1-2^3=18`. For `{a,b}`, it is
`4^3-2*2^3=48`. The three-label counts are `3!*1*2*2=24` and
`3!*2^3=48`. Hence the sum of all weights is


```math
1+26m+72\binom m2+48\binom m3=(2m+1)^3=n^3.             \qquad\text{(HT7)}
```


We reserve the `m` weight-8 variables, the `m` weight-18 variables,
and the center weight-1 variable. All other weights are 24 or 48.
This special reserve removes the divisibility difficulty in an arbitrary
bounded-weight prime sum.

## 3. Exact analytic imports and uniform domains

The imported finite-list lemma **FL** is the statement in
[`explicit_prime_targets.md` at PR77 scientific revision
`c2118dfad1aeb660d66308dc6a94d6c959f5010c`](explicit_prime_targets.md).
Its local exported file has SHA256
`0e6ff5f0c26c6a2a6e66d0ae2b1a2ef581f282662a8e772e827ba04fd72f45e1`.
The full statement and its role in CT are recorded in
[cube_targets.md](cube_targets.md#imported-interfaces-and-their-exact-boundary).
We use the actual finite interface, not the superseded ternary interface.

At center `y>0`, write `ell=ceil(log_2 y)>=2`. FL requires an even
original modulus `2<=g<=16ell`, a length-`k` unit-residue list with sum
`ky mod g`, and an integer total `ky`. It requires


```math
k\ge54000\ell^{11},\qquad
 2^{20}\ell^{11}\le d\le y/4,                            \qquad\text{(HT8)}
```


and, on every interval `I subset [y-d,y+d]` of length at least `d/500`,


```math
\pi(I;g,a)\ge |I|/(4g\ell)
 \quad(a\text{ a unit mod }g),                           \qquad\text{(HT9)}
```



```math
\pi(I;q,a)\ge |I|/(4q\ell^9)
 \quad(2\le q\le128\ell^2, a\text{ a unit mod }q).       \qquad\text{(HT10)}
```


The conclusion is a list of primes in the requested original classes,
within distance `d` of `y`, with exact total `ky`. Target values may
repeat. Every use here has original modulus **2**, with all residues 1.
The auxiliary modulus range in (HT10) still has to be checked in full.

The analytic source is Thorner--Zaman,
[*Refinements to the prime number theorem for arithmetic progressions*,
arXiv:2108.10878v2, 21 September 2021](https://arxiv.org/pdf/2108.10878v2),
Theorem 1.1, Remark 1.2, equation (1.6), and the consequence printed in
Section 1.2, page 3. For fixed `A>=1` and `epsilon>0` it supplies the
weighted prime asymptotic `h/phi(q)`, uniformly in reduced classes,
`q<=(log x)^A`, and


```math
x^{7/12+\epsilon}(\log x)^A\le h\le x.
```


The threshold is ineffective. This source was checked directly at its
printed hypotheses; no exceptional-zero restriction has been dropped.
The ineffective polylogarithmic-modulus consequence is what permits
exponent `7/12` here.

Fix


```math
\beta=71/120,\qquad d=\mu^\beta/4,\qquad
 \epsilon=1/240,\qquad A=3.                              \qquad\text{(HT11)}
```


The already proved uniform counting consequence (TC) in
[cube_targets.md](cube_targets.md#uniform-local-counting-consequence)
then gives, for every interval `I subset [mu-2d,mu+2d]` of length at
least `d/500`,


```math
\pi(I;q,a)\ge\frac{|I|}{2\phi(q)\log(2\mu)}             \qquad\text{(HT12)}
```


uniformly for every reduced class and
`2<=q<=128(ceil(log_2 mu)+1)^2`, once `mu` is large enough.
Indeed its right endpoint is `x~mu`, its length is at least
`mu^beta/2000`, and
`beta-7/12-epsilon=1/240>0`; this power absorbs both the factor 2000
and the cubic logarithm. The allowed auxiliary moduli are eventually
at most `(log x)^3`. The source's uniform asymptotic, division by
`log(2mu)`, and eventually positive error margin give (HT12).

## 4. A weighted exact-total prime lemma

**Lemma HW (weighted prime completion).** There is an ineffective
absolute constant `M` with this property. Let `n=2m+1` be odd, let `T`
be an odd integer, set `mu=T/n^3`, and assume


```math
\mu\ge M,\qquad
 m\ge60000(\lceil\log_2\mu\rceil+1)^{11}.                \qquad\text{(HT13)}
```


There are primes `q_S` for every nonempty `S subset J` of size at most
three such that the weighted sum in (HT7) is exactly `T` and


```math
|q_S-\mu|\le\mu^{3/5}.                                 \qquad\text{(HT14)}
```


All constants are uniform in `m,T` under the displayed assumptions.

**Proof.** Use `d` from (HT11). Equation (HT12) for modulus 2 supplies
an odd prime below `mu` in `[mu-d,mu-d/2]` and one above `mu` in
`[mu+d/2,mu+d]`. Fix any such two primes. Process all bulk variables
(weights 24 or 48) in a fixed order, taking the lower prime when the
current weighted discrepancy is nonnegative and the upper prime when
it is negative. If the discrepancy is `E`, the next increment has
opposite weak sign and absolute value at most `48d`. Induction gives


```math
|E|\le48d.                                             \qquad\text{(HT15)}
```


This bound does not grow with the number of bulk variables. Reusing a
target value is allowed; no entry of the eventual array is assigned in
this step.

Choose a prime `q_0=q_{ {0} }` in `[mu-d,mu+d]` with


```math
q_0\equiv T-26m\pmod4.                                \qquad\text{(HT16)}
```


The residue is odd, so (HT12) for modulus 4 supplies it. Write `B` for
the weighted bulk sum and put `R=T-B-q_0`. All bulk weights are
divisible by 8. Equations (HT7), (HT15), and (HT16) give


```math
R\equiv26m\pmod4,\qquad
 R=26m\mu-\varepsilon,\qquad |\varepsilon|\le49d.         \qquad\text{(HT17)}
```


In particular `R` is even. Choose an integer `S_18` nearest to `m*mu`
in the residue class


```math
S_{18}\equiv R/2-4m\pmod8.                              \qquad\text{(HT18)}
```


The distance is at most 4. Since `R/2` has the parity of `m`,
`S_18` has the parity of `m`. Define


```math
S_8=(R/2-9S_{18})/4.                                   \qquad\text{(HT19)}
```


Reducing the numerator modulo 8 using (HT18) gives `4m mod 8`.
Thus `S_8` is an integer of parity `m`, and


```math
8S_8+18S_{18}=R.                                       \qquad\text{(HT20)}
```


If `eta=S_18-m*mu`, then `|eta|<=4` and


```math
S_8-m\mu=-\varepsilon/8-(9/4)\eta,
 \qquad |S_8-m\mu|\le49d/8+9.                           \qquad\text{(HT21)}
```


Set `y_8=S_8/m`, `y_18=S_18/m`. Increasing the fixed constant `M`
if necessary, (HT13) and (HT21) imply


```math
|y_8-\mu|\le d/4,\qquad |y_{18}-\mu|\le d/4.           \qquad\text{(HT22)}
```


For example the elementary inequalities already hold for `m>=128`
and `d>=16`. Both centers are positive and asymptotic to `mu` uniformly.

Apply FL twice, with length `k=m`, radius `d`, original modulus 2,
and every requested residue equal to 1. The two totals are `S_8`
and `S_18`. Their integer and congruence hypotheses follow from
(HT18)--(HT19). We check every other hypothesis:

1. If `ell_i=ceil(log_2 y_i)`, then
   `ell_i<=ceil(log_2 mu)+1` eventually. Hence (HT13) implies the
   actual length bound `m>=54000ell_i^11`; length `n` has not been
   substituted for length `m`.
2. `g=2<=16ell_i`, while `d>=2^20ell_i^11` and `d<=y_i/4`
   eventually, because `0<beta<1`.
3. Every required interval lies inside `[mu-2d,mu+2d]` by (HT22).
   Its length is at least `d/500`. Every auxiliary modulus in (HT10)
   is within the range of (HT12).
4. Uniformly at these two centers,
   `2phi(q)log(2mu)<=4q ell_i` eventually. Consequently (HT12)
   implies the strong count (HT9) at `g=2`, and it also implies
   (HT10), since `ell_i^9>=ell_i`.

Use the first list as the `m` primes `q_{ {a} }` with weight 8 and
the second as the `m` primes `q_{ {0,a} }` with weight 18. Their
weighted total is exactly `R` by (HT20), so the full total is `T`.
Every finishing prime differs from `mu` by at most `5d/4`. Bulk and
center primes differ by at most `d`. Finally
`5d/4=(5/16)mu^beta<mu^(3/5)` eventually, since `beta<3/5`.
This proves (HT14). Every threshold is uniform under (HT13). QED.

The use of modulus 4 for the single center is necessary in this
finishing scheme: choosing an arbitrary odd center only forces `R`
even and need not make both length-`m` list totals have the correct
parity. The modulo-8 choice (HT18) performs the remaining integrality
and parity repair with bounded displacement.

## 5. Signed prime targets at the exact first-pool scale

**Theorem SPT4.** There is an ineffective integer `N_T` such that for
every odd `n>=N_T`, the pool (HT4) has a prime target vector on all
`4n^3+12n^2+16n+8` full signed-coordinate lines with the following
properties:

1. All partition identities (HT3) hold exactly and each axis-direction
   grand total is exactly `T`.
2. Every target is odd and at distance at most `mu^(3/5)` from `mu`.
3. The vector is in the integer image of the full signed-line map; it
   has an odd integer lift of total `T` by SI4.
4. For every even `2<=g<=16ceil(log_2 X)`, every target is a unit
   modulo `g`. A single target vector works for all these moduli.

Repeated targets are allowed. No section sum is asserted to be prime.
No arrangement of `P_n` is asserted by this target theorem alone.

**Proof.** The prime number theorem and partial summation, as used
in the pinned CT, give


```math
X\sim4n^4\log n,\qquad T\sim2n^8\log n,\qquad
 \mu\sim2n^5\log n.                                    \qquad\text{(HT23)}
```


Thus `mu` tends to infinity and
`m/(ceil(log_2 mu)+1)^11` tends to infinity along the entire odd tail.
The total `T` is odd, since it is the sum of `n^4` odd primes.
Lemma HW applies for every sufficiently large odd `n`. Define the
target vector by (HT5). Lemma HP proves all partition identities,
and the exact weighted total proves every directional total `T`.
Its entries are primes in the stated window; eventually they exceed
2 and hence are odd. For `n>=17`, SI4 gives integer liftability.

To check the odd lift explicitly from SI4's integer image, let `1`
denote the all-one array. Its full line vector is the constant vector
`n`. The vector `(y-n)/2` is integral and satisfies (HT3), because
both `y` and the constant vector `n` satisfy them. SI4 gives an
integer array `z` with this line vector; then `1+2z` is an odd
integer lift of `y`. Summing its axis lines gives total `T`.
This lift need not be positive and need not have any prescribed entries.

Finally every target is at least `mu-mu^(3/5)`, which exceeds
`16ceil(log_2 X)` eventually by (HT23). A prime greater than `g`
cannot divide `g`, so every target is a unit modulo every allowed
physical modulus. The analytic list modulus used above remains 2;
there is no need to prescribe all physical residues in advance.
The threshold is independent of `g`, target repetitions, and the odd
order once it lies in the specified tail. QED.

The target displacement is smaller than one pool-scale unit:


```math
\frac{\mu^{3/5}}X
 \sim\frac{2^{3/5}}4\,n^{-1}(\log n)^{-2/5}\longrightarrow0.
                                                               \qquad\text{(HT24)}
```


It is therefore also `o(KX)` for any controller scale `K` tending to
infinity. This supplies a quantitative window, but does not certify the
controller's residue capacity, correction range, disjoint supports,
centering, or physical permutation realization.

SPT4 is a structured existence theorem. It does not extend an arbitrary
given CT tensor to all signed families and does not prescribe arbitrary
unit-residue arrays modulo the physical gap. The physical interface
must accept the actual compatible odd target vector constructed here.

## 6. Architecture choice and source-bound controls

The initially considered approach was to start from an arbitrary
symmetric CT tensor, prescribe both margins of every pair-family prime
matrix, and then coordinate complementary traces. Independent prime
lists do not solve that problem: choosing one row can spoil a column
or a complementary trace. This is an unproved alternative architecture,
not an impossibility result. The set pattern (HT5) removes those
overlapping analytic obligations by imposing exact structural symmetry
before prime values are chosen.

The source-bound executable
[hyper4_targets_controls.py](../../originals/code/hyper4_targets_controls.py)
checks the exact weight counts, finishing congruences, all partition
identities, and finite target-vector certificates. Its producer and
checker enumerate the line family by different methods. Its primality
checker uses exact trial division independently of the producer's sieve.
Negative controls alter the exact pool total, omit and duplicate lines,
change a prime target to a composite, and corrupt a partition identity.

Replay from the repository root:

```sh
python problems/prime-arrays-beyond-square/code/hyper4_targets_controls.py self-test
python problems/prime-arrays-beyond-square/code/hyper4_targets_controls.py check problems/prime-arrays-beyond-square/inputs/hyper4_targets_n3.json --negative-controls
python problems/prime-arrays-beyond-square/code/hyper4_targets_controls.py check problems/prime-arrays-beyond-square/inputs/hyper4_targets_n5.json --negative-controls
python problems/prime-arrays-beyond-square/code/hyper4_targets_controls.py check problems/prime-arrays-beyond-square/inputs/hyper4_targets_n17.json
```

The persisted inputs give the following exact checks. The order-17 file
stores the `q_S` values and the explicit full-family set rule; its checker
independently enumerates every line cell set and decodes its fixed
coordinates. It does not store 23,400 redundant line descriptions.

| Order | Exact pool total | Target variables | Distinct lines | Partition identities |
| ---: | ---: | ---: | ---: | ---: |
| 3 | 15535 | 3 | 272 | 154 |
| 5 | 1340727 | 7 | 888 | 298 |
| 17 | 42747841521 | 129 | 23400 | 2170 |

The negative controls at orders 3 and 5 reject changed total, omitted
line, duplicated line, composite target, invalid recorded residue,
corrupted pair-family marginal, and a shifted line masquerading as a
full line. Repeated prime targets are deliberately accepted. The
order-17 certificate can be regenerated by

```sh
python problems/prime-arrays-beyond-square/code/hyper4_targets_controls.py make 17 problems/prime-arrays-beyond-square/inputs/hyper4_targets_n17.json --compact
```

These finite outputs are labeled **target vectors**, never prime-entry
hypercube arrangements. They do not verify FL's enormous asymptotic
length condition at the displayed small orders, and they do not prove
the eventual theorem. The conventional proofs above and SI4 are the
reasons the asymptotic target theorem holds. Small orders below 17 are
used only to check the explicitly listed partition identities; no
integer-image claim for such an order follows from this manuscript.

The dependency chain is: pinned FL and Thorner--Zaman imply the uniform
count and HW; HP and HW imply the prime vector with exact partition
identities; the separate SI4 theorem supplies eventual integer and odd
liftability. A separate physical theorem is still required for the
requested bijection of the exact first `n^4` odd primes.
