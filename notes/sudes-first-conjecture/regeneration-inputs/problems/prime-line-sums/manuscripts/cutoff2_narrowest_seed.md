# Selecting the narrowest seed groups

Author: `/root/controller_redesign`. This additive finite lemma sharpens
FS's range bound without changing FS, PB, BN, or any frozen controller.
It requires independent nonauthor review at the exact scientific revision.
It makes no numerical-cutoff, analytic-import, or formal-proof claim.

## NS1. Candidate selection and exact retained cardinality

Let Q,s,t be positive integers. Suppose at least Q(s+t-1) labelled,
vertex-disjoint pairs of prescribed input primes have the same positive
difference g. Their midpoints lie in (0,X). Earlier deletions must already
have been paid, exactly as in FS4. Take exactly Q(s+t-1) surviving pairs,
sort their midpoints, and divide the sorted list into r=s+t-1 consecutive
groups of exactly Q. Break ties by the distinct pair labels.

The midpoint intervals of these groups are disjoint except possibly at
endpoints. If R_1,...,R_r are their ranges, then

    R_i>=0,                 sum_i R_i <= X.                 (NS1)

Keep the s groups of smallest range; ties may be resolved by their
original group index. Let z be the largest retained range. Each of the
t-1 discarded groups has range at least z. Consequently

    sum_kept R_i <= X-(t-1)z,                t z <= X.       (NS2)

For t>=2, multiplying the first inequality by z proves

    sum_kept R_i^2 <= z sum_kept R_i
                  <= z[X-(t-1)z]
                  <= X^2/[4(t-1)],
    max_kept R_i^2 <= X^2/t^2.                              (NS3)

The last step is the identity
`z[X-(t-1)z]=X^2/[4(t-1)]-(t-1)(z-X/[2(t-1)])^2`.
It covers zero ranges, coincident values and every real endpoint. For
t=1 all r=s groups are retained and NS1 gives sum_kept R_i^2<=X^2;
there is no division by t-1.

Exactly s groups of Q pairs are retained. Only their 2Qs input entries
are reserved. Every discarded pair, and every additional candidate not
chosen for the initial list, remains unreserved in the prescribed pool.
Thus the candidate demand is still Q(s+t-1), and the entry-deletion
invoice is still 2Qs. The selection does not assert that all candidate
pairs lie in the later growth interval.

## NS2. Controller invariants and centering

The retained groups are stages of the same common gap g. Assigning one
pair of each stage to each of the Q labelled pair slots preserves every
ordinary seed reservoir's complete grid {0,g,...,sg}. The equal-gap
pairs required in each diagonal rectangle remain available. Labelled
bijections within a stage cannot repeat any input entry. No position or
prime is shared between stages.

Use the PB layout with Q=d(n+8), and the same independent uniform
permutations within retained stages as FS3. For an ordinary row or
column, the squared ordinary slot weights sum to3d per stage; at most
one extra rectangle over the entire family contributes at most4. The
two diagonals have the smaller coefficient2d. These are the unchanged
PB/BN incidence facts, proved in their source manuscripts and checked
in the FS component. Hence the all-line variance invoice is

    3d sum_kept R_i^2 + 4 max_kept R_i^2
        <= [3d/(4(t-1))+4/t^2]X^2,             t>=2.         (NS4)

The same weighted-permutation concentration and union bound give a
simultaneous seed allocation with error, for every required line, at
most

    X sqrt([3d/(4(t-1))+4/t^2] log(8n+8)/2).                 (NS5)

For t=1 use the unchanged coefficient3d+4. This is a finite existence
argument with the conventional proof from BN; a sampled success is not
its justification. Other independent stage families retain their own
allocations and bounds. Common growth batches still use their actual
midpoint width and their separately certified deterministic bound.

Every retained stage has its actual selected mean. The total selected
prime sum and the unused-pool mean are recomputed from those means.
PB's exact cancellation remains valid; the candidate mean must not be
substituted for the retained mean. Under BG's mean bounds the full-pool
midpoint bias remains at most.513X, and all2Qs retained entries must
still be paid as possible deletions from the later growth pool.

## NS3. Weighted seed choice and interval certification

For each possible selected gap g, fix its own s_g and t_g before choosing
a label. NS changes only the retained-range and seed-allocation bounds.
Its demand in the single full-pool weighted matching remains

    D_g=Q(s_g+t_g-1)+L_g,                                  (NS6)

where L_g is the separately proved destruction budget for earlier
reservations. In particular the CS savings, if invoked, must retain
all their genuine small-gap exceptions and leave every other pooled,
local, geometric and centering invoice unchanged.

A numerical controller must check the full weighted matching inequality,
all entry and position counts, every stage capacity and rounding jump,
the source-dependent supply and target conditions, and a contiguous
upper handoff. NS5 does not itself establish a new square cutoff.
The t parameter is an integer group allowance, not a continuous
optimization variable in the final certificate.

## NS4. Reproducible finite controls

The companion standard-library checker tests the range algebra on every
small nonnegative sorted range vector in its manifest, including its
extremal and zero cases. It selects actual equal-gap prime pairs from
the exact first n^2 odd-prime pool, recomputes all group ranges, keeps
exactly the smallest s, and checks candidate/kept/unused cardinalities,
all initial complete grids, and the actual selected-mean identity.

Negative controls include selecting a wide group instead of a smallest
one, omitting candidate groups, sharing input entries, changing the
common gap, substituting an old candidate mean, and malformed or
physically substituted source maps. The required source set and hashes
are explicit. No inaccessible artifact or numerical optimization output
is a proof dependency.

Run `python3 -B problems/prime-line-sums/code/cutoff2_narrowest_seed.py`.
The arithmetic and mechanism checks do not kernel-check the universal
proof or establish the imported analytic theorems.
