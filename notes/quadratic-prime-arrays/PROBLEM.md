# Canonical Gaussian and Eisenstein prime arrays

## Statement

For K=Q(i) or Q(omega), omega²+omega+1=0 and Im(omega)>0, let O be
its ring of integers. Gaussian representatives are a+bi with a>0,b>=0;
Eisenstein representatives are a+b omega with a>b>=0. Retain one element
from each associate class, retain conjugate classes separately, and omit
only the class of 1+i or 1-omega respectively. Include inert rational primes.
Sort the representatives by (N(z),a,b), using N=a²+b² or a²-ab+b².
The dimension-D input A(n,D) is exactly the first n^D such representatives.

Seek a bijection from A(n,D) to [n]^D, D=2 or3, whose every full
signed-coordinate line has a prime-element sum. A line has every coordinate
fixed, t, or n+1-t, and at least one varying coordinate. Deduplicate cell sets.
There are 2n+2 square lines and 3n²+6n+4 cube lines for n>=2; the singleton
has one line. Signed directions never mean negative coefficients in sums.
Prime sums may repeat. No unit rotations, conjugations, selective deletions,
extra entries, norm-only substitutions, or square-section requirements occur.

## Scope

The exact input pool and its vector total, not an idealized sector centroid,
govern every target equation. The eventual results and their limits are stated
in the [main note](README.md); complete proofs are linked there.
