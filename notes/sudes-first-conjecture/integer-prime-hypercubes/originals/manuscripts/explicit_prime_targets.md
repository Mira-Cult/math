# Exact prime target lists by a second reservoir

## Scope and status

This is a new quantitative alternative to A1--A4 in
[analytic_continuation.md](analytic_continuation.md). The preserved source at
4ac266e7c4994a8502eb2a0c57d6b1d3fbd801c5 is not changed. This manuscript's
finite lemma is proposed for independent review. No permanent claim ID is
allocated. Its analytic hypotheses are displayed explicitly below.

The replacement preserves the square problem's exact total and prescribed
residues. It uses the permission that prime **line sums may repeat**. It does
not assert the old length-uniform theorem for every list length at least three:
the new interface requires a displayed polynomial-in-logarithm lower bound
on the list length. The actual length n will satisfy it. Consequently no
ternary Goldbach theorem, or implicit three-prime completion, occurs here.

## Finite target-list lemma

Let y>0, D>0, and let ell=ceil(log_2 y) be an integer at least 2.
Let g be even, 2<=g<=16ell, and let a_1,...,a_k be reduced residue classes
modulo g. Suppose

1. T=ky is an integer and sum a_i=T modulo g;
2. D<=y/4, D>=2^20 ell^11, and k>=54000ell^11;
3. for every reduced class a modulo g, every interval I inside
   [y-D,y+D] of length at least D/500 contains at least
   |I|/(4g ell) primes in that class;
4. for every integer q with 2<=q<=128ell^2, every reduced class b modulo q,
   and every such interval I, the count is at least
   |I|/(4q ell^9).

Then there are primes t_i, with repetitions permitted, such that

  t_i=a_i (mod g), |t_i-y|<=D, and sum t_i=T.

The proof is finite and uses no asymptotic assertion.

### 1. Find a small repeatable difference

Some class a occurs at least k/g times. In
[y-D/4,y+D/4], hypothesis 3 supplies M_0>=D/(8g ell) primes in this
class. Since M_0>=2, two consecutive primes r<s have

  h=s-r <= D/M_0 <= 8g ell <=128ell^2.

Here the span of all M_0 primes is at most D/2, and M_0-1>=M_0/2.
The even integer h is a multiple of g. All primes in the window exceed h,
so b=r modulo h is reduced and lifts a modulo g. The same pair (r,s)
can be used in arbitrarily many target coordinates: these are line-sum
targets, not entries of the prescribed pool.

### 2. Complete an h-grid interval with a bounded number of slots

Put F=4ell^9. Let A be the primes in class b modulo h in
[y-D/2,y+D/2]. Hypothesis 4 gives M=|A|>=D/(hF).
Use s_0=4F=16ell^9 copies of the seed pair. Their differences cover the
h-grid from 0 to R_0=s_0 h. The assumptions imply

  4D/M <= R_0 <= 2048ell^11 <=D.

For R_0<=R<=D, divide the interval containing A into
ceil(D/R)<=2D/R bins of length at most R. One bin contains at least
MR/(2D)>=2 points. Its extremes differ by an h-multiple d satisfying

  R/(4F) <= hMR/(4D) <=d<=R.

This is the translated finite binning argument C2 in
[reservoir_continuation.md](reservoir_continuation.md). Appending d preserves
complete h-grid coverage by C1. Reuse of earlier primes is harmless here.
Each group of 4F appended differences at least doubles R, because
(1+1/(4F))^(4F)>=2 by the binomial theorem. At most
4F ell stages therefore give R>=D, since D<=y<=2^ell.
The resulting prefix has at most

  P <=4F(ell+1)<=32ell^10

slots, every endpoint in [y-D/2,y+D/2], and total difference R in [D,2D].
If the initial endpoint is already D, no growth stage is needed.

### 3. Add capacity with centered pairs

Set delta=1/1000. Hypothesis 4 gives a prime u in class b modulo h in
[y-D/3-delta D,y-D/3+delta D], and a prime v in the same class in
[y+D/3-delta D,y+D/3+delta D].
Each interval has length D/500; its stated lower count exceeds one because
D>=2^20ell^11 and h<=128ell^2. Thus

  D/2 < v-u <D, and |(u+v)/2-y|<=delta D.

Append J=100(P+1) copies of this pair. They are legal complete-sequence
extensions because the current endpoint is already at least D. Let R_tot
be the new total difference, and let A_tot be the sum of the lower endpoints
of all r_*=P+J controlled slots. Their possible sums include exactly every
h-grid value in [A_tot,A_tot+R_tot], and

  r_*<=3332ell^10,
  R_tot>=JD/2,
  |A_tot+R_tot/2-r_*y|<=PD/2+Jdelta D.

There are enough coordinates in the common original class a:
k/g>=3375ell^10>=r_*+3. Reserve r_* of them. At least three coordinates
remain unreserved.

### 4. Lift all remaining residues before choosing primes

Choose reduced classes b_i modulo h for the unreserved coordinates, lifting
their original classes a_i modulo g, with

  sum_unreserved b_i = T-r_*b (mod h).

This is an elementary CRT statement, not a prime-pattern assertion.
For p^v||g and p^w||h, w>=v, the required total is already compatible
modulo p^v. Altering one lift by a multiple of p^v achieves the prescribed
sum modulo p^w without losing its unit property. For each new prime p|h,
p does not divide g and hence p is odd. Fix arbitrary units for all but
three remaining coordinates. Every residue modulo p^w is a sum of three
units: choose the first unit 1 and choose the second residue modulo p
different from 0 and the desired sum minus 1; then the third is also a
unit. Lifts modulo p^w and CRT complete the construction.

This proof works also when some prime powers of h have higher valuation
than those of g. It does not assume g and h/g are relatively prime.

### 5. Greedy discrepancy, followed by an exact grid repair

For each unreserved b_i, hypothesis 4 provides a prime on each side of y
in [y-D,y+D]. Process these coordinates in any order. If the running
discrepancy sum(t_i-y) is nonnegative choose the lower prime; otherwise
choose the upper prime. Induction keeps the discrepancy in [-D,D],
independently of the number of processed coordinates.

The desired sum of the reserved coordinates is congruent to A_tot modulo h.
Its distance from the midpoint A_tot+R_tot/2 is at most

  D+PD/2+J D/1000 < JD/4 <=R_tot/2,

because J=100(P+1). It therefore lies on the covered grid and is realized
by a choice of one endpoint in each controlled pair. All choices are
primes, within D of y, and in the originally prescribed classes modulo g.
Their sum is the exact integer T. This proves the lemma.

## Interface to the square problem

The proposed parameter choice is

  ell_X=ceil(log_2 X), K=floor(n/ell_X^100),
  y=mu=T/n, ell=ceil(log_2 mu), D=mu/ell^200.

Once 2X/5<=m=T/n^2<=3X/5 and n>=3, one has
X<mu<=nX and ell_X<=ell<=2ell_X. Since K>=n/(2ell_X^100)
whenever n>=2ell_X^100,

  D/(KX) <=2ell_X^100/ell^200 <=2/ell_X^100.

Thus the target displacement is much smaller than KX/10. The controller
baseline is within KX/10 of mu, so the complete row, column and independent
diagonal targets lie within its KX/2 capacity.

The row and column lists each satisfy the lemma with k=n and their own
residue list, with exact total T. Each diagonal needs just one prime in
its specified reduced class, supplied by the same progression estimate.
No target prime is added as an entry; the controller still permutes exactly
the original n^2 primes.

The quantitative composition must separately verify D>=2^20ell^11,
n>=54000ell^11, and the two progression hypotheses. It must also prove
the numerical analytic starting point and persistence for all larger n.
This manuscript alone is not a numerical square-existence theorem.

## Effectivity distinction

The strong progression hypothesis is needed only for q=g, which is at most
a constant times log y. It gives h=O(log^2 y). The weaker hypothesis then
runs over q<=128ell^2 and allows a loss ell^8 in density. Using the weak
estimate already for the first close-pair selection would inflate h beyond
its own modulus range; that circular argument is deliberately not used.

The intended classical source is an explicit progression estimate retaining
the sign and size of a possible exceptional-zero term. The quasi-RH
alternative supplies a stronger density under the exact pinned zero-free
assertion. Their source proofs and statuses belong in
[effective_pair_supply.md](effective_pair_supply.md) and
[quasi_rh_effectivity.md](quasi_rh_effectivity.md), respectively.

## Reproducible finite controls

Run the exact standard-library program

~~~sh
python3 -B problems/prime-line-sums/code/threshold_prime_targets.py
~~~

The fixed input constructs 50,001 prime targets with mean 100,003, radius
20,000, original modulus 2, and lifted modulus 6. The exact total is
5,000,250,003. It uses 24 prefix slots and 2,500 wide slots; the free
greedy discrepancy is -12. Its checker recomputes the total, residues and
radius and trial-divides every distinct target prime independently of the
producer sieve. The program also checks 266 CRT lifting cases, including
overlapping prime powers, and exhausts a small complete-sequence control.

These are controls of the finite mechanisms at an explicitly supplied
prime set. They do not verify the displayed analytic hypotheses on an
infinite range, establish the numerical order cutoff, or assert that the
50,001 targets are themselves a square using an initial prime pool.
