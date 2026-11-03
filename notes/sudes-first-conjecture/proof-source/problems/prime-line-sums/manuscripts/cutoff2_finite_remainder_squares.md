# Exact certificates for every odd order from 1 through 1999

Author: `/root/prefix_balance_research`. This is a separate finite
certificate component. It changes no earlier proof, controller, analytic
interface, or certificate. Independent nonauthor review must bind its
exact scientific revision. This manuscript does not claim such a review,
an infinite-tail result, external acceptance, or formal verification.

The prescribed pool and labelled lines are exactly those of
[PROBLEM.md](../PROBLEM.md). Repeated prime line sums are allowed. This
component has no analytic prime-count import and no probabilistic
assumption. It does not use the separately checked eventual tail.

## FR1. Finite result and exact witness set

For each of the 1000 consecutive odd integers `1,3,...,1999`, the bound
certificate decodes to a permutation of exactly the first n squared odd
primes whose n row sums, n column sums, and two main diagonal sums are
prime. For n=1 the four required line labels refer to the singleton [3].

The input is
[cutoff2_finite_remainder_squares_certificates.bin.gz](../inputs/cutoff2_finite_remainder_squares_certificates.bin.gz):

```
compressed bytes:   10500031
compressed SHA-256: 5f8be996b548afac76e276088da5a094e3ff4375075ecea14aec77c71522b27c
raw bytes:          13522748
raw SHA-256:        c8f41eb90f2a2d6d08428b5eb1d86cb373abf38467996920d9470e75045a40fd
```

The public file uses one gzip member, compression level 9, zero mtime,
no filename, and fixed header `1f8b08000000000002ff`. Compression changes
only storage and transport. Before replay the wrapper verifies the
compressed source hash, decompresses with a maximum output of exactly
the allowed raw size plus one rejection byte, and requires the displayed
raw size and SHA-256. It rejects truncated streams, trailing data and
additional members. It never performs an unbounded decoder flush. The
uncompressed certificate is not a separately required public artifact.

The decoded certificate contains 1,686,341 accepted swaps in total.
The exact replay processes
1,333,333,000 cells across the 1000 separate squares and checks 2,002,000
required line labels. The largest input prime is 67,796,177, and the
largest observed line sum is 68,630,847,793. No order in the stated range
is omitted, inferred from nearby orders, or supported merely by a search
probability. The largest square has 3,996,001 cells.

The compact file is a lossless replay encoding of the canonical
certificate's ascending pool, flat row-major permutation, and recomputed
line sums. The pool is specified by exact enumeration, not replaced by
a different starting block. The encoding avoids storing approximately
1.33 billion matrix entries separately.

## FR2. Complete binary and permutation specification

All integers in the uncompressed payload are unsigned and little endian.
That payload begins with
the eight ASCII bytes `SUDEFR01`, followed by three u32 fields:

```
first order = 1, last order = 1999, order count = 1000.
```

Exactly one record then appears for each successive odd order. A record
has fields `n:u32`, `seed:u64`, and five u32 swap counts, in the order
`direct, main, anti, rows, columns`. These are followed by that many
pairs `(a:u32,b:u32)`, grouped in the same phase order. Positions are
zero-based indices in the flat row-major square. Every swap has distinct
indices strictly below n squared. There are no padding or trailing bytes.

To decode the initial permutation, start with ranks `0,...,n^2-1`.
The rank i denotes the (i+1)-st odd prime, so rank zero denotes 3.
Use a u64 state initialized to the recorded seed. Each word is defined
by the following integer operations; every addition and multiplication
is reduced modulo 2^64, and every shift is a logical right shift:

```
state = state + 0x9e3779b97f4a7c15
z = state
z = (z xor (z >> 30)) * 0xbf58476d1ce4e5b9
z = (z xor (z >> 27)) * 0x94d049bb133111eb
word = z xor (z >> 31)
```

For j decreasing from `n^2-1` to 1, produce one word and interchange
ranks j and `word mod (j+1)`. Finally apply each recorded swap in order.
No statistical property of this integer map or of the resulting
permutation is required. A seed is not itself asserted to be a successful
witness: the complete swap sequence is present and checked.

For n=1 all five counts are zero. For n=3 only the direct count may be
nonzero, and it is at most eight. For n>=5 the direct count is zero,
each diagonal count is at most one, and each row/column phase has at
most n swaps. Diagonal swaps exchange a noncentral cell of the designated
diagonal with a cell on neither diagonal. Row swaps exchange two
off-diagonal cells in one column; column swaps exchange two off-diagonal
cells in one row. The verifier checks these restrictions individually.

All count sums in the verifier use u64 arithmetic; malformed u32 counts
cannot wrap to conceal an excessive sequence. The maximum valid cell
index fits in u32. Every line sum is below
`1999 * 67796177 < 2^37`, so the u64 summation cannot overflow.

## FR3. Why exact replay proves the finite assertion

The standalone checker is
[cutoff2_finite_remainder_squares_verify.cpp](../code/cutoff2_finite_remainder_squares_verify.cpp).
It imports no search code and contains no probable-prime test.

**Exact pool.** An odd-only Eratosthenes sieve marks odd composite
multiples starting at p squared for each unmarked odd p up to the square
root of its bound. Every odd composite has a least prime factor no larger
than its square root, so it is marked; a prime is never marked. Reading
unmarked candidates in increasing order therefore gives the exact first
required odd primes. The initial bound is `20*(1999^2+1)=79920040`.
Its adequacy is checked by actually counting the required primes; no
prime-index estimate is presumed. The implementation can enlarge the
bound if necessary, but that branch is not needed for this certificate.

**Exact input permutation.** The initial rank list contains every rank
once. Its deterministic shuffle and all certified swaps are bijections.
The checker additionally traverses the completed list, rejects repeated
or out-of-range ranks, and verifies that every required rank appears.
Replacing each rank by its enumerated prime gives exactly the required
pool, once each.

**Every required line.** The checker derives rows, columns and both
diagonal sums afresh from the completed rank list. It does not trust
incremental search sums, recorded target sums, or a digest of a matrix.
The two diagonals are included as separate line labels, including the
shared center in each sum as required. A finite family is accepted only
if the header, the number of records and every successive order agree
with the explicitly requested range; EOF must follow its last record.

**Exact primality.** Values within the sieve range are tested against
the complete sieve. For larger values, the checker divides by every
enumerated odd prime p until p squared exceeds the value. It first
checks that its trial-prime list reaches beyond the square root of the
largest possible line sum for the requested range. Thus a returned prime
has no possible prime divisor; even values and values below two are
handled explicitly. The full replay performs 26,336,639,789 such exact
trial divisions. There is no Miller--Rabin, unproved hypothesis, or
unverified primality assertion in the replay.

These finite exhaustive checks establish the assertion for each
recorded order under the ordinary correctness interpretation of the
specified algorithms and arithmetic. This is a conventional
computer-assisted finite proof, not an end-to-end proof-kernel theorem.
Its independently reviewed status must be supplied separately and at
the exact source revision.

## FR4. Discovery and recovery are separate from acceptance

The reproducible generator is
[cutoff2_finite_remainder_squares.cpp](../code/cutoff2_finite_remainder_squares.cpp).
It uses a full-integer sieve, actual prime values, and maintained line
sums, rather than the verifier's odd-only sieve and rank representation.
It first seeks prime diagonal sums, then repairs bad rows through
off-diagonal swaps within columns, then repairs columns through
off-diagonal swaps within rows. A repair never turns an already accepted
line in its current phase into a rejected one; it may repair two bad
lines at once. Consequently at most n swaps are needed per completed
axis phase. The successful seed and accepted swaps suffice for replay;
unsuccessful trials and discarded restarts are not mathematical inputs.

The order-three generator searches lexicographic permutations until it
finds a witness, then records at most eight swaps to that permutation.
This component does not claim an exhaustive count of order-three
solutions. The n=1 witness is immediate.

For discovery only, larger candidate sums may be screened by two
strong probable-prime tests. Before accepting an order or writing its
record, the generator recomputes its sums and tests every one exactly
by sieve or trial division. A false positive in discovery therefore
cannot enter an accepted record. More importantly, the separate replay
does not use these discovery decisions at all. The finite result has
no claim that the search succeeds at any untested order or from every
initial state.

Recovery uses only the public source, input manifest and certificate.
The manifest records every order's exact offset, seed, phase counts,
record length and SHA-256 in the uncompressed payload, plus the complete
recomputed verifier report.
It is bound by
[cutoff2_finite_remainder_squares.py](../code/cutoff2_finite_remainder_squares.py),
with input
[cutoff2_finite_remainder_squares_inputs.json](../inputs/cutoff2_finite_remainder_squares_inputs.json).
The wrapper requires exactly the complete source set, rejects empty or
malformed maps, verifies every source before compilation, and compares
all recomputed results by exact type as well as value. It writes the
validated uncompressed bytes to a temporary file for the unchanged C++
verifier. The optional generator also emits raw bytes; its recovery
comparison is against the validated raw certificate, independent of
gzip library versions.

Tested toolchain: Python 3.12.14 and GNU C++ 13.3.0, compiling C++20 with
`-O3 -std=c++20 -Wall -Wextra -pedantic`. Only Python's standard library
and a C++ compiler are needed; there is no network, private artifact,
precomputed prime table or third-party runtime package.

From the repository root:

```
python3 -B problems/prime-line-sums/code/cutoff2_finite_remainder_squares.py
```

To additionally regenerate the entire certificate and require
byte-for-byte equality with the bound file:

```
python3 -B problems/prime-line-sums/code/cutoff2_finite_remainder_squares.py --regenerate
```

The default replay does not execute the search generator. The optional
recovery flag is not needed to validate the supplied witnesses. At the
tested Python/zlib toolchain, recompressing the raw bytes with the stated
gzip parameters reproduces the public compressed file exactly.

## FR5. Mechanism and rejection controls

A further Python oracle independently generates primes by incremental
trial division, reconstructs every witness at odd orders through 101,
checks each exact input permutation, and tests every line by trial
division. Its canonical certificate digests and fresh line statistics
are bound in the input manifest and checked against the C++ replay.
It does not substitute scattered tests for the C++ verifier's complete
coverage through 1999.

Negative controls reject incomplete or reordered ranges, malformed
headers, excessive or overflowing counts, truncated or extra data,
invalid and identical swap indices, diagonal-phase violations, and a
well-formed but unsuccessful initial permutation. Two further valid
order-three permutations have all rows, all columns and one main
diagonal prime while only the other diagonal is composite. The checker
must reject both on primality rather than format. Missing, empty,
mismatched, directory-substituted and symlinked sources and malformed
hash maps are also rejected.
Compression controls additionally reject wrong headers, nonzero mtime,
CRC corruption, truncation, extra members, and an attempted expansion
beyond the fixed raw size.

The full certificate remains a finite component. Combining it with an
all-odd tail beginning at 2001 requires a separate exact-revision
composition review of that tail and its entire dependency closure.
