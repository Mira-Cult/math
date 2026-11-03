**Public reading copy.** Presentation and links have been normalized. Historical status statements below belong to their source revisions; see the [current publication status](../../README.md#review-and-verification-status). The matching original bytes are in the [source archive](../../originals/manuscripts/cube_targets.md).

# Symmetric prime targets in every fixed dimension

Author: `/root/cube_targets`. Manuscript-local labels only; no permanent claim
IDs are allocated. This manuscript proves target-vector results, **not** a
permutation theorem for a prescribed cube pool. The physical controller and
its residue repairs are separate obligations.

## Imported interfaces and their exact boundary

The preserved PR77 source
[`explicit_prime_targets.md` at c2118dfad1aeb660d66308dc6a94d6c959f5010c](explicit_prime_targets.md)
proves the following **finite list lemma**, abbreviated FL. Let
`ell=ceil(log_2 y)>=2`, let `g` be even with `2<=g<=16ell`, and let
`a_1,...,a_k` be units modulo `g`. Suppose:

1. `T=ky` is an integer and `sum a_i=T (mod g)`;
2. `d<=y/4`, `d>=2^20 ell^11`, and `k>=54000ell^11`;
3. every interval inside `[y-d,y+d]` of length at least `d/500` has at
   least `|I|/(4g ell)` primes in each reduced class modulo `g`;
4. for every `2<=q<=128ell^2`, the same intervals have at least
   `|I|/(4q ell^9)` primes in each reduced class modulo `q`.

Then primes `t_i` exist in the specified original classes, in `[y-d,y+d]`,
with exact sum `T`. Repeated targets are permitted. This list lemma uses
one repeatable difference, complete-sequence growth, residue lifting, and
greedy balancing. Its lower bound on `k` is part of the interface; it is
not the older three-prime completion theorem, and we do not remove that
bound. The seeds in FL are repeated **target values**, never repeated pool
entries.

For asymptotic short-window supply we use Jesse Thorner and Asif Zaman,
*Refinements to the prime number theorem for arithmetic progressions*,
[arXiv:2108.10878v2, 21 September 2021](https://arxiv.org/pdf/2108.10878v2),
Theorem 1.1, Remark 1.2, equation (1.6), and the short-interval consequence
in Section 1.2, printed page 3. For every fixed `A>=1` and `epsilon>0`,
uniformly in reduced classes modulo `q<=(log x)^A` and

`x^(7/12+epsilon)(log x)^A <= h <= x`,

that consequence gives

`sum_{x-h<p<=x, p=a (mod q)} log p = (1+o(1))h/phi(q)`.

The threshold here is **ineffective** because of the Siegel-bound step.
This is adequate for an eventual-existence target theorem and supplies no
numerical extension of PR77's explicit square bound. Only one-dimensional
prime counts are imported. No theorem with a number of affine forms growing
with the order is invoked.

### Uniform local counting consequence

Fix `7/12<beta<1`, put `d=mu^beta/4`, and let `mu` tend to infinity.
For every interval `I` in `[mu-2d,mu+2d]` with `|I|>=d/500`, and every
reduced class modulo

`2<=q<=128(ceil(log_2 mu)+1)^2`,

the prime count is at least

`|I|/(2phi(q)log(2mu))`                                             (TC)

for all sufficiently large `mu`, uniformly in all the listed data.

Indeed choose `epsilon=(beta-7/12)/2`. If `x` is the right endpoint,
then `x~mu`, `h=|I|>=mu^beta/2000`, and
`q<=(log x)^3` eventually. The source's lower bound
`h>=x^(7/12+epsilon)(log x)^3` follows since the positive power
`mu^(beta-7/12-epsilon)` dominates every fixed power of `log mu`.
The uniform asymptotic gives weighted count at least `h/(2phi(q))`;
division by `log(2mu)` proves (TC). The endpoints can be real; changing
an endpoint convention changes a count by at most one and is absorbed by
the eventually diverging main term. Alternatively take all intervals
half-open, as in the source and FL.

## Weighted symmetry orbits and the exact total

For fixed `r>=1`, a symmetric `r`-tensor on `[n]^r` is invariant under
permuting its coordinate positions. An orbit under this action has weight
equal to its number of labeled positions, at most `r!`. Precisely `n`
orbits have weight one: `(i,...,i)`. These will be the finishing reservoir.
For `r=1`, all positions are finishing positions and there is no first stage.

**Theorem ST (symmetric targets with growing modulus).** Fix `r>=1`,
`7/12<theta<1`, and `0<eta<16`. There is a threshold `M(r,theta,eta)`
with the following property. Let `n>=3` be odd, let `T` be an integer,
put `mu=T/n^r`, and assume

`mu>=M`, `n>=60000(ceil(log_2 mu)+1)^11`,

and let `g` be even with `2<=g<=(16-eta)log_2 mu`.
Let `a` be a symmetric tensor of units modulo `g` satisfying

`sum_{x in [n]^r} a_x = T (mod g)`.

There is a symmetric tensor of primes `P`, repetitions permitted, such that

`P_x=a_x (mod g)`, `sum_x P_x=T`, and `|P_x-mu|<=mu^theta`

for every labeled position `x`. The threshold is uniform in `n`, `T`,
`g`, and the complete residue tensor, subject to the displayed hypotheses.

**Proof.** Choose and fix `beta` strictly between `7/12` and `theta`,
and put `d=mu^beta/4`, `w=r!`. By (TC), every requested reduced class
modulo `g` has a prime strictly below `mu` and a prime strictly above
`mu`, both at distance at most `d`. For example, use the intervals
`[mu-d,mu-d/2]` and `[mu+d/2,mu+d]`, where the lower bound tends to
infinity uniformly. The stated bound on `g` places it inside the range
of (TC).

Process the orbits other than `(i,...,i)` in any fixed order. In an orbit
of weight `v<=w`, choose the lower prime if the current total discrepancy
`E=sum_completed v(P-mu)` is nonnegative, and the upper prime otherwise.
The next increment has the opposite weak sign and magnitude at most
`wd`. Induction gives `|E|<=wd`, irrespective of the number of orbits.
Assign the same selected prime to every position of that orbit.

After this stage let `T'=T-sum_completed vP`. This is an integer and

`T'=n mu-E`, `mu'=T'/n=mu-E/n`, `|mu'-mu|<=wd/n`.                  (ST1)

The residue condition for the `n` remaining positions is exactly
`sum_i a_(i,...,i)=T' (mod g)`. As `n` tends to infinity with `mu`
under the displayed lower bound, eventually `n>=4w`; hence
`|mu'-mu|<=d/4`. Set `ell'=ceil(log_2 mu')`.

We now check FL at center `y=mu'`, radius `d`, and length `k=n`.
First, `mu'~mu`, `ell'<=ceil(log_2 mu)+1`, and consequently the
length bound holds, since `60000>54000`. The fixed positive slack
`eta` implies `g<=16ell'` eventually: `log_2 mu'=log_2 mu+o(1)`,
whereas the available slack is `eta log_2 mu`. Also `d<=mu'/4` and
`d>=2^20(ell')^11` eventually, since `beta<1` and a positive power
dominates every logarithmic power.

Every interval used by FL lies in `[mu'-d,mu'+d]`, which is contained
in `[mu-2d,mu+2d]`. Its length is at least `d/500`. The modulus range
`q<=128(ell')^2` is within the range of (TC). For large `mu`,

`2phi(q)log(2mu) <=4q ell' <=4q(ell')^9`.

Indeed `phi(q)<=q` and `ell'~log(mu)/log(2)`. Thus (TC) implies both
FL's strong and weak count hypotheses, with their actual constants.
Its congruence and integer-total hypotheses were already checked.

Apply FL to the `n` constant-coordinate positions. The resulting primes
have the required classes, sum exactly `T'`, and differ from `mu'`
by at most `d`. By (ST1) their distance from `mu` is at most
`d+wd/n<=5d/4<mu^theta` eventually. The first-stage primes are within
`d<mu^theta`. The assigned tensor is symmetric and its exact sum is
`T`. Every threshold used depends only on the fixed `r,theta,eta`.
This proves ST. QED.

### Existence of an admissible symmetric residue tensor

If `n>=3` is odd, `T` is odd, and `g` is any even positive integer,
a symmetric unit-residue tensor with total `T mod g` always exists.
Set all nonconstant orbits to the unit `1`. The remaining required
sum for the `n` constant-coordinate positions is odd. Set the first
`n-3` of these to `1`; the residual is still odd. Every odd residue
modulo an even modulus is a sum of three units. To see this, take the
first unit to be `1`; at each odd prime divisor `p` of `g`, choose
the second residue different from `0` and from the value forcing the
third to be `0`. Even for `p=3`, at least one of the three residues
remains. At the power of `2`, choose the second residue odd; then the
third is odd because the desired sum is odd. Choose lifts to every
prime power and apply CRT. This proof is finite and uniform in `g`.

This gives **existence of target residues**. It does not assert that a
given prime pool can be permuted to those residues. That is a physical
residue-controller obligation.

## Compatible axis targets for every fixed dimension

Let `D>=2` be fixed, take `r=D-1`, and use the same symmetric tensor
`P` as the directional target tensor in each of the `D` orientations.
Coordinates in each tensor are listed in the natural order after omitting
the varying axis. For distinct axes `d,e`, summing the `d`-direction
targets over coordinate `e` and summing the `e`-direction targets over
coordinate `d` produce identical `(D-2)`-tensors: both are the same
one-coordinate marginal of the symmetric tensor `P`. Thus all pairwise
marginal equations hold exactly, and each directional grand total is `T`.
This checks the full compatibility equations, not just the grand totals.

In dimension three this is particularly transparent. Write

`U_(j,k)=P_(j,k)`, `V_(i,k)=P_(i,k)`, `W_(i,j)=P_(i,j)`.

Then

`sum_j U_(j,k)=sum_i V_(i,k)`,

`sum_k U_(j,k)=sum_i W_(i,j)`,

`sum_k V_(i,k)=sum_j W_(i,j)`.

The first equality is literal equality of column sums; the other two use
symmetry. No additional congruence is introduced by these identities.

**Corollary CT (targets at the exact initial-prime-pool scale).** For
every fixed `D>=2`, all sufficiently large odd `n`, and every even
`g<=16ceil(log_2 X)`, where

`A={p_2,...,p_(n^D+1)}`, `X=p_(n^D+1)`,
`T=sum_(p in A) p`, `mu=T/n^(D-1)`,

there are compatible directional tensors of prime axis-line targets with
exact directional total `T`, every target within `mu^(3/5)` of `mu`,
and with a common symmetric reduced-residue pattern modulo `g`.
Moreover, every prescribed symmetric unit-residue pattern having total
`T mod g` is possible.

**Proof.** The prime number theorem and partial summation give

`X~D n^D log n`, `T~(D/2)n^(2D)log n`,
`mu~(D/2)n^(D+1)log n`.

Consequently `ceil(log_2 X)/log_2 mu -> D/(D+1)`. Choose, for
example, `eta=8/(D+1)`. Then `16ceil(log_2 X)<=(16-eta)log_2 mu`
eventually. Also `n/(log_2 mu)^11 -> infinity`, so ST's full
list-length condition holds. The total `T` is odd since `n^D`
entries are odd, and the finite residue construction above applies.
Use ST with `theta=3/5`; this exceeds `7/12`. The previous compatibility
calculation proves the conclusion. Finally,

`mu^(3/5)/X ~ c_D n^((3-2D)/5)(log n)^(-2/5) ->0`.

Thus this target window is even `o(X)`, and in particular `o(KX)`
for any `K` tending to infinity. The constants and thresholds depend on
fixed `D`; no conclusion for `D` growing with `n` follows. QED.

## What CT does and does not finish

CT resolves the exact-total symmetric-target proposal as an actual theorem,
including a logarithmically growing modulus and the polynomial-logarithmic
length condition required by the newer PR77 target interface. Its only
non-elementary new analytic input is the explicitly identified, ineffective
short-interval progression theorem above.

To turn it into an axis-line **arrangement** theorem, a physical controller
must still establish the following independently:

- a centered permutation of the prescribed distinct pool;
- residue repair to a compatible symmetric unit pattern, with all changes
  and cell occupancy paid;
- disjoint permutation gadgets realizing the needed compatible corrections
  within a quantified capacity region.

Saturation of the signed-integer line-sum lattice does not establish any of
these three facts. Nor does CT cover every compatible unit-residue tensor;
the tensor must be symmetric in the displayed common-orientation sense.

For simultaneous square sections in dimension three, every axis slice
total would be a row sum of `P`. Theorem ST does not make these row sums
prime. Taking `P` constant would instead give composite row sums `n p`.
The six diagonal squares involve further aggregates of diagonal-line
targets, which CT does not even prescribe. These remain distinct nonlinear
target obligations. Body-diagonal lines are not diagonal squares.

## Literature boundary and finite controls

A targeted search on 2 November 2026 located prime magic-cube constructions
with freely selected prime entries and a common, usually composite, magic
sum. For example, the original 2014
[Magic Cubes of Prime Numbers competition description](https://primesmagicgames.altervista.org/wp/magic-cubes-of-prime-numbers/)
requires distinct prime entries and equal row/column/pillar/body-diagonal
sums; its displayed order-three example has common sum 5091. It does not
use the first 27 odd primes and its common sum is not prime. This is a
different problem. No matching prescribed-initial-pool eventual theorem
was found in this bounded search; that is not a claim that none exists.

The finite program `../code/cube_targets_experiment.py` constructs
symmetric prime target tensors for exact totals of small initial pools
and independently verifies primality, symmetry, total, and all axis marginal
compatibility identities. Its search is a small-instance producer and
does not implement the asymptotic FL reservoir. A successful target
certificate is not a cube-entry arrangement certificate.
