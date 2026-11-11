# A finite, reusable matching of 3,650,551 gap-two prime pairs

Author: `/root/controller_redesign`. This is an additive finite component,
not an assertion about infinitely many twin primes. It changes no frozen
source and claims no square cutoff. Independent review must address its
exact source revision before use in an accepted composition.

## FT1. The exact finite statement

Put B=2^30. There are exactly 3,650,551 pairs (p,p+2) of primes with
43<p and p+2<=B. Every endpoint is odd. These pairs are vertex-disjoint:
otherwise three successive odd integers p,p+2,p+4 would all be prime;
one is divisible by3 and exceeds3.

The accompanying public Python checker enumerates this finite set by a
segmented Eratosthenes sieve. Its input manifest contains the complete
512-segment count table, exact bound, segment size and required-file map.
Every segment and the final total are recomputed. No inaccessible data,
external primality service, probable-prime assumption or floating-point
calculation is used.

The same enumeration gives pi(2^30)=54,400,028. The first retained pair
is (59,61), and the final lower endpoint is 1,073,741,717. These auxiliary
identities are checked but do not replace the complete count.

## FT2. Why the finite enumeration proves the count

Let r=floor(sqrt(B)). The base sieve marks exactly the composite integers
through r: a composite has a prime divisor at most its square root, and
marking begins at p^2 so it never marks p itself. For each consecutive
odd segment [lo,hi], with lo>=45, initialize every odd candidate to1.
For each odd base prime p with p^2<=hi, mark all odd multiples beginning
at the smallest odd multiple of p at least max(p^2,lo).

Every marked candidate is composite. Conversely, every odd composite
q<=B has an odd prime divisor p<=sqrt(q)<=r; the marking loop for p
contains q. Thus a final1 is equivalent to primality, not merely to
survival of a bounded probable-prime test.

Two adjacent surviving positions represent p,p+2. There cannot be three
adjacent surviving positions because all candidates exceed3. Consequently
Python's nonoverlapping count of the byte string 11 counts every adjacent
prime pair exactly once. The one possible pair crossing each segment
boundary is counted separately. The checker also explicitly rejects any
111 pattern within a segment or across a boundary. Its segment cover has
no gaps or repetitions and ends at the largest odd integer at most B.

All arithmetic indices and counts are Python integers. The maximum base
prime, each marked progression, both segment boundaries, and the full
source table are exact. Small complete trial-division oracles with varied
segment sizes separately exercise the sieve and cross-boundary logic.
An independently implemented C++ sieve was used for discovery and agreed
with the count; the public certificate does not require it.

## FT3. Applying the matching to a bounded controller

Suppose a controller uses the exact first n^2 odd primes and its largest
prime X satisfies X>4B. Every certified pair belongs to this exact pool.
All BB bridge windows lie inside [X/4,3X/4], so every bridge entry is
strictly larger than every matching endpoint. At g=2 the residue family
is empty. Hence the preselected bridge and residue families destroy no
pair in this matching.

For degree d, let Q=d(n+8). If the retained seed-stage count is s>=1 and
the narrowest-group allowance is t>=1, the sufficient candidate condition
is simply

                    Q(s+t-1)<=3,650,551.                 (FT1)

The matching is fixed before any label choice; there is no weighted-gap
pigeonhole or favorable-gap assumption. Partition the first Q(s+t-1)
chosen pairs into consecutive sorted-midpoint Q-groups and retain the s
narrowest groups as in [NS](cutoff2_narrowest_seed.md). Only the retained 2Qs prime entries are used.
All discarded candidate entries remain available to later construction.

All candidate midpoints belong to an interval of width less than B.
The pinned NS range proof therefore gives

    sum retained range^2 <= B^2/[4(t-1)], max range^2<=B^2/t^2

for t>1, and its usual width-B bound when t=1. In the simultaneous seed
allocation allowance, multiply NS's dimensionless coefficient by B^2
instead of X^2. For an actual scale lower bound X>=X0, the normalized
seed error is at most

       (B/X0)*sqrt(c_NS(d,t)*log(8n+8)/2).                (FT2)

This is a re-specialization of the range algebra, not a change of the
input pool or a reuse of reserved entries. Every later global, reflected,
geometric and mean invoice still pays every retained seed entry. The
stage means may be far below m; the original PB mean cancellation and its
full bound must still be retained. No seed entry is removed from a later
central-stock budget without a separately proved interval separation.

For a real order band, a verified upper integer envelope n1 gives the
uniform form d(n1+8)(s+t-1)<=3,650,551. Its lower scale enclosure must
separately prove X>4B for every order. These finite hypotheses and a
classical construction on every larger order are sufficient for a full
infinite-tail composition; this source supplies no all-scale twin-prime
claim.

## FT4. Scope of verification

The program checks the complete finite prime count, pair disjointness
mechanism, exact segment table, source integrity and stated finite
matching/range implications. Negative controls cover boundary, marking,
matching, table, count, input and source-file failures. Missing, empty,
extra or malformed source maps fail. Source symlinks are rejected.

The sieve proof and controller implication are ordinary mathematics and
program review. They are not an end-to-end kernel-checked theorem. No
analytic theorem is imported to prove the finite prime count itself.
