# A finite family of disjoint common-gap prefix populations

Author: `/root/controller_redesign`. This additive source generalizes the
finite-population computation of FP to five explicitly bounded bands.
It proves a finite stock and conditional allocation interface, not a
prime-line square or numerical cutoff. The complete controller, independent
review and published exact scientific revision remain separate obligations.

## FPF1. Fixed finite populations

The following alternative populations are independently generated. They
must not be combined as if they were disjoint from one another.

| Name | Integer orders | Sieve bound B | Endpoint interval | Stages P | Qmax |
|---|---:|---:|---:|---:|---:|
| L |2000..2400|60000000|[13000000,55000000]|24|14448|
| C27 |2400..3000|95000000|[27000000,74000000]|24|18048|
| M |3000..5000|150000000|[44,150000000]|26|30048|
| H |5000..10000|450000000|[44,450000000]|28|60048|
| T |10000..19483|1800000000|[44,1800000000]|30|116946|

Stage j=0,...,P−1 has common difference h_j=2^(j+1). Each stage
contains exactly Qmax disjoint prime pairs (p,p+h_j). Every endpoint
is prime, exceeds43, belongs to its stated interval, and is distinct
from every endpoint of every other stage in that same population.
The exact odd-prime counts below the five sieve bounds are respectively
3562114,5489748,8444395,23853037,88862421. Each is at most n_min².
Thus every endpoint belongs to the first n² odd primes for every order
in the corresponding band, by finite counting alone.

For an actual n use exactly the first Q=6(n+8) pairs of EACH stage.
The declared Qmax is6(n_max+8). Truncation preserves the common gap,
primality and all disjointness. Unused copies and unselected candidates
remain free input entries; they are not silently reserved. The actual
retained entry count is2QP, not2Qmax P.

## FPF2. Exact enumeration and selection

A complete odd sieve through B marks every composite and no prime.
All candidate stages use the surviving live entries after all previous
Qmax stages have been retained. Enumerate every p with both p and p+h
live and in the stated endpoint interval. Because h is a power of2,
three consecutive vertices p,p+h,p+2h cannot all be primes>43: one
is divisible by3. Therefore the full fixed-gap edge set is already a
vertex-disjoint matching. No greedy matching loss is being hidden.

Sort these lower endpoints. Among all consecutive Qmax-sized windows,
choose the one with least last-minus-first range, resolving ties at the
first window. Retain exactly those pairs and remove exactly their
endpoints from the live set. Every other candidate remains available.
Repeat for all P stages. The public generator writes every selected
lower endpoint in little-endian uint32 format, together with complete
stage counts, chosen indices, ranges, sums and a transcript. The strict
manifest pins every count and both transcript and stream hashes.

The verifier compiles the pinned public C++17 source and reproduces all
five complete computations. It then independently checks the produced
stream's length, endpoints, order, common differences, sums, complete
cross-stage entry disjointness and all metadata. A separate small-prime
trial-division fixture reimplements the selection rule without the C++
sieve. No prebuilt executable, private binary, cached prime list or
network resource is needed. The compiler is an explicit public build
dependency. The final verification is conventional exact computation,
not kernel verification.

The C27 stream agrees with the previously frozen FP computation; the
new family does not alter that source. The other populations are new
finite enumerations, not transfers of a theorem outside its literal
sieve or order domain.

## FPF3. Complete grids and both diagonal reservoirs

Starting from radius0, a complete even grid through R remains complete
when a gap h≤R+2 is appended: [0,R]∩2Z and its translate by h join
without a missing even point. Here h_j=R_previous+2 exactly. Thus the
P stages cover every even integer from0 through

                       R_P=2^(P+1)−2.                    (FPF1)

This is a finite induction, including its integer endpoint. It is not
necessary to enumerate2^31 grid values. The same argument with the
existing2d identical diagonal copies gives the amplified complete even
grids. Each diagonal rectangle uses two pairs from the same common-gap
stage, so its row/column-preserving identity remains valid. The two
main diagonals and all off-designated cells use the unchanged PB/RP
slot geometry; that geometry is a separate caller hypothesis.

Every finite population must be protected before subsequent value
selection. A caller must either subtract its full possible depletion
or certify its exact intersection with each later supply interval.
The public protected_interval_count interface handles real rational
endpoints for half-open intervals (left,right] on the actual truncated
populations. This does not permit overlap of retained entries.

## FPF4. Allocation and exact mean interface

For each actual n let W_j be the retained midpoint range in stage j.
It equals the range of that stage's retained lower endpoints. Let μ_j
be its exact retained midpoint mean. Under the same balanced PB/RP slot
geometry, simultaneous prefix allocation error is at most

   sqrt([3d sum_j W_j²+4 max_j W_j²] log(8n+8)/2), d=6.   (FPF2)

This is the generic stage-range form proved in FP. Its proof uses only
that each stage has Q=d(n+8) labels and a common gap, that ordinary line
weights have squared mass at most3d per stage, and that globally
nonoverlapping rectangles contribute the extra4 term at most once
per line across all stages. It does not require P=24 or B=95000000.
The conditional permutation inequality and its ordinary mathematical
proof are imported from the pinned FP/PB sources; the new finite
arithmetic does not prove a concentration theorem by itself.

The verifier supplies exact per-order stage ranges, min/max stage
means, sum of stage means, total retained prime sum and variance
coefficient. With A=sum_j(μ_j−m), the prefix total deviation is exactly
2Q A. Its effect on the later unused mean is −2Q A/(n²−B_total).
When there is no nonmain reserved family (the actual C0=0 premise
of FP13), the gap2 shared mean cancellation gives the all-line prefix bias

    2 max_j|μ_j−m| + 16dn |A|/(n²−B_total).              (FPF3)

This retains the signed sum before taking an absolute value. Every
local extra-cell contribution remains paid. All later bridge, wide,
completion and geometric entry counts must still include every retained
prefix endpoint; the finite enumeration reduces no unrelated invoice.

## FPF5. Scope and verification boundary

The five bands cover every integer2000..19483; square applications
select their odd orders. Exact per-order truncation and integer endpoints
cover every Q jump. The family supplies no complete square, target list,
flow theorem or infinite tail by itself. Those components must be
composed and reviewed separately. Input maps are complete, nonempty and
strict; missing, changed, malformed, extra, empty or symlinked sources,
transcripts and streams fail closed. Negative controls exercise both
manifest integrity and the finite matching/selection semantics.
