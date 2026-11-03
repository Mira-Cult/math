# Exact prime targets on a contiguous finite order range

Author: `/root/controller_redesign`. This finite component does not assert
a prime-line square or a new square cutoff. It replaces the analytic
prime-target interface only on its explicitly enumerated bounded range.
The classical analytic construction and infinite-tail fallback remain
separate. Independent nonauthor review and a published scientific pin
are required before accepted composition.

## FTT1. Exact statement

For every odd integer 2001≤n≤19483 let X=p_(n²+1), let T be the sum
of the first n² odd primes, and let y=T/n. The supplied finite table
certifies odd primes q,P,R such that

                 (n−2)q+P+R=T,                          (FTT1)

and each of q,P,R differs from y by at most X/1000. Thus n−2 copies
of q and one copy of each of P,R form an exact n-term prime target
list. Both diagonals may use q. Repetition of prime target values is
allowed and has no effect on the requirement that input entries form
an exact permutation of the first n² odd primes.

The same enumeration certifies

                  .484 < T/(n²X) < .488                 (FTT2)

at every one of these orders. Actual X and T are supplied for every
order, so a bounded controller can use their exact values instead of
importing an asymptotic mean or prime-index premise below its domain.
There are exactly 8,742 consecutive odd orders. This is a contiguous
finite certificate, not a selection of successful examples.

## FTT2. Recover X and T from the exact input pool

The public C++ source uses an ordinary segmented sieve of all odd
integers beginning at3. Its finite upper bound is10^10; all base primes
up to100000 are obtained by a complete ordinary sieve. For a segment
starting at odd lo, a base prime p marks odd multiples beginning at
max(p²,ceil(lo/p)p), adjusted to be odd. Consecutive marked positions
are separated by p odd indices. No prime is marked, and every odd
composite≤10^10 has a prime factor at most100000, so every composite
is marked. The segmentation has no gaps or repeated candidates.

The scan counts and sums every surviving odd prime. At count n² it
outputs that prime X and the accumulated sum T. The verifier requests
prefix mode, which performs no probable-prime screening or target
search. It compares the complete output, in order, to every stored
(n,X,T) row. The last count is379,587,289, the last prime is8,269,325,591,
and the last sum is1,531,561,973,193,239,017.

All marking indices and prime counts fit unsigned64-bit integers.
Even the crude bound n²*10^10<2^62 holds at n=19483. The summation also
has an explicit overflow rejection. The target generator uses128-bit
products only as a search aid; exact certificate verification uses
arbitrary-precision integers.

The replay requires a C++17-capable GCC or Clang compiler, which is an
explicit public build dependency. The verifier compiles the pinned
source into a temporary directory and reruns it. No prebuilt private
binary, cached prime list, inaccessible artifact or network resource
is used. Reproduction of the finite prefix is a computation whose
algorithm is justified above; it is not formal kernel verification.

## FTT3. Primality certificates, independently of search tests

Every target prime and every required smaller factor has a recursive
Lucas certificate. The base case is2. For p>2 a certificate contains
an exact complete factorization

                      p−1 = product q^e                 (FTT3)

into already certified primes q<p, and an integer a with1<a<p such that

    a^(p−1) = 1 mod p,
    gcd(a^((p−1)/q)−1,p)=1 for every distinct q.           (FTT4)

These conditions prove p prime. Indeed, if l is any prime divisor of p,
then a is a unit modulo l and its order divides p−1. For each q in
(FTT3), the gcd condition forces the full power q^e into that order.
Therefore its order is p−1, which divides l−1. Hence l≥p and p is prime.
This elementary argument, with strict decreasing recursive factors,
proves every certificate in the finite directed acyclic graph.

The verifier checks exact integer types, ordered distinct factors,
positive exponents, complete products, every modular power and gcd,
and the full dependency closure. It rejects missing certificates and
extraneous unreachable nodes. The stored closure has69,609 prime nodes,
covering25,942 distinct target values.

The search generator uses fixed-base probable-prime tests and integer
factor searches to find candidates efficiently. None of these tests
establishes the theorem: the independent Lucas conditions above are
rechecked before a generated candidate is accepted. No assumption
about the reliability or coverage range of a Miller–Rabin base set
enters this component.

## FTT4. Exact list and radius checks

For each consecutive order the verifier checks n−2≥1, primality of
all three stored targets, exact equality (FTT1), and

            1000*abs(n*z−T) <= n*X for z=q,P,R.           (FTT5)

This pays the real, possibly nonintegral y without rounding. The largest
observed normalized deviation is less than0.000828X; the certificate
uses the clean uniform bound X/1000. Both diagonal targets satisfy the
same bound. Formula(FTT1) gives the exact number of targets and exact
total without an arithmetic-grid length hypothesis.

The input manifest pins the complete source and data files. Missing,
empty, malformed, mismatched or symlinked files/maps fail closed.
Negative controls include an omitted order, a reordered order, altered
X/T, a false target sum/radius, incomplete factorization, bad witnesses,
a Fermat pseudoprime, missing certificates and malformed types. The
full prime-prefix scan is part of the default verifier; a table hash
alone is not represented as a proof of its X/T entries.

## FTT5. Boundary of this finite result

A square construction still needs its input-pool gadgets, placement,
both diagonal independence, target-to-baseline centering and flow
capacity, all verified for each order to which this table is applied.
For n outside2001..19483 this component makes no claim. A complete
odd-order-tail theorem must supply contiguous bounded controller
coverage and the separately reproducible upper-tail fallback.
