# A solver-free derivation of the eventual six-residue formula

With h=6t+r, set H=h+1, B=h²+h+1, and C=gamma_4(h). Then for sufficiently large h, gamma_5(h)=d_4 C+d_3 B+d_2 H+d_1, where the true positional digits are:

| r | d_1 | d_2 | d_3 | d_4 |
|---|---:|---:|---:|---:|
| 0 | t+1 | t | t | 4t |
| 1 | 5t+2 | t | t+1 | 4t |
| 2 | t+1 | t | t+1 | 4t+1 |
| 3 | 5t+3 | t+1 | t | 4t+2 |
| 4 | t+2 | t+1 | t | 4t+3 |
| 5 | 5t+5 | t+1 | t+1 | 4t+3 |

The proof below uses only finitely many tiny integer arithmetic checks, with a solver-free replay. It does not specify or assert the smallest valid h. It uses the [analytic asymptotic proof](asymptotic-proof.md), independently of the [unbounded integer checks used for the explicit cutoff](exact-proof.md). Primary starting formulas are O'Bryant, [arXiv:2312.10910v3](https://arxiv.org/html/2312.10910v3), §3 and Appendix A.

## Sharp hole localization

Use the signed budgets P(u)=Σ max(u_i,0), N(u)=Σ max(−u_i,0), the exact kernel k_1,k_2,k_3, and the limit lattice L=Z³+Z(1/2,1/2,1/2) from the separate asymptotic proof. Suppose neither residue phase of a point covers both P≤1/3−ε and N≤1−ε, for sufficiently small ε>0. Here coverage uses arbitrary integer translations of that phase. Choose the phase with at most one coordinate at least 1/2 and sort it a≤b≤c.

If all are below 1/2: when c<ε the original all-plus representative works. Otherwise keeping a,b and subtracting one from c has negative cost≤1−ε, so a+b>1/3−ε. The other phase all-minus must fail, so a+b+c<1/2+ε. Together with a≤b≤c, these give a,b,c=1/6+O(ε).

If exactly c≥1/2: failure of the original two-plus choice gives a+b>1/3−ε. In the shifted phase, which sorts as (c−1/2,a+1/2,b+1/2), keeping only the first positive has negative cost 1−a−b≤1−ε. Thus c>5/6−ε. Failure of keeping only the smallest original coordinate positive means a>1/3−ε or b+c<1+ε. If b+c<1+ε, then b<1/6+2ε and a>1/6−3ε, also c<5/6+4ε, giving (1/6,1/6,5/6)+O(ε). Otherwise a>1/3−ε, and the shifted all-minus failure gives a+b+c<3/2+ε, yielding (1/3,1/3,5/6)+O(ε). All constants here can be absolute. These cases prove three possible centers up to coordinate permutations and simultaneous half-shift.

For the actual mex x=gamma_5(h), form genuine successive Euclidean digits d^0=(d_1,d_2,d_3,d_4) dividing by C,B,H. The already proved asymptotic gives d_4=2h/3+O(1). The lower digits scaled by h are bounded, have first two coordinates at most one, and third at most 1/2+O(1/h). If a limiting lattice correction n∈Z³ gives P≤1/3−ε,N≤1−ε for the first three scaled digits, then n is uniformly bounded by invertibility of the limiting basis (both input and output are bounded). Replacing the limit basis with the actual first-three-scaled kernel basis incurs O(1/h) error, and changes d_4 by bounded n_3. Taking ε=D_0/h with one sufficiently large constant D_0 would therefore give a true r=1 collision (both budgets exact, fourth digit positive), contrary to mex. Thus the actual digits lie within O(1) of h times one of the center triples and their half-shifts and permutations. Wrap at 0/1 causes no additional center because all listed centers stay uniformly away from boundaries. The third digit restriction removes centers whose third numerator exceeds three, leaving precisely the seven numerator triples
   (1,1,1),(1,5,1),(2,5,2),(4,4,2),(5,1,1),(5,2,2),(5,5,2),
all over denominator six.

## Exact bounded-offset carry arithmetic

Fix h=6t+r with r∈{0,1,2,3,4,5}, and one center (a,b,c) from this list. Write trial digits in increasing significance as
   (a t+A, b t+E, c t+F, 4t+G).
Here A,E,F,G are bounded integer offsets for the true mex. For every fixed such tuple the trial is a legitimate canonical Euclidean digit tuple for sufficiently large t: its first two coordinates are strictly between 0 and h in leading order, third strictly between 0 and h/2, and fourth near 2h/3. Thus no endpoint restrictions on offsets persist. Also x>h C/2 eventually, ruling out multiplier ≥2.

Any equality representation with multiplier one adds j k_1+k k_2+l k_3 for integer j,k,l. An actual collision has first three scaled output coordinates bounded, so by invertibility of the scaled basis these carry coefficients lie in a fixed finite box independent of t and bounded offsets. The first three leading coefficients in t are
   z=(a−6j−3l, b−6k+3l, c−3l),
and the fourth is 4. The limiting feasibility budgets are P(z)≤2 and N(z)≤6. Such a carry necessarily has z_i∈[−6,2]; from z_3 obtain l=0,1,2, then z_1 gives j∈{−1,0,1} and z_2 gives k=0,1,2. For each center this tiny check gives exactly four potentially feasible carries:
| center | carries (j,k,l), any order |
|---|---|
| (1,1,1) | (−1,1,2), (0,1,0), (0,1,1), (1,0,0) |
| (1,5,1) | (−1,2,2), (0,1,0), (0,1,1), (1,1,0) |
| (2,5,2) | (−1,2,2), (0,1,1), (0,2,1), (1,1,0) |
| (4,4,2) | (0,1,1), (0,2,1), (1,1,0), (1,1,1) |
| (5,1,1) | (0,1,1), (0,1,2), (1,0,0), (1,1,0) |
| (5,2,2) | (0,1,1), (0,1,2), (1,1,0), (1,1,1) |
| (5,5,2) | (0,2,1), (0,2,2), (1,1,0), (1,1,1) |

For every listed carry all z_i are nonzero and exactly one inequality is tight. Thus signs of actual first three coefficients are fixed for all sufficiently large t with bounded offsets. The constant vector contributed by the carry is
   u=(−(r+1)j−k−floor(r/2)l,
        j−rk+floor((r+1)/2)l,
        k−floor((r+3)/2)l),
and the fourth correction is l. The vector is exact by the kernel formula. If P(z)=2, then negative budget has leading slack, and avoiding this collision is equivalent to
   G+Σ_(z_i>0) (A,E,F)_i ≥ r+1−l−Σ_(z_i>0) u_i.
If N(z)=6, then positive budget has leading slack, and avoiding collision is equivalent to
   Σ_(z_i<0) (A,E,F)_i ≤ −r−Σ_(z_i<0) u_i.
The shifts by one reflect exact strict negation of P(d)≤h and N(d)≤h−1. Therefore four elementary linear inequalities characterize admissibility of any bounded offsets at each center and residue.

## Integer minimum without a solver

Minimize (G,F,E,A) lexicographically in each center's four inequalities. The following forms derive and attain all four minima by simple substitutions. For clarity write ordinary variable triples A,E,F as U,V,W and fourth offset as D; constants are symbolic.
* For (1,1,1) the three lower bounds are U+V+D≥a, U+W+D≥b, V+W+D≥c, with total U+V+W≤s. Summing gives D≥ceil((a+b+c−2s)/3). At this minimum the smallest W=b+c−2D−s; choosing U=b−D−W and V=c−D−W attains it. Indeed the two bounds involving W with total upper bound prove that lower limit, and equality forces the displayed U,V. The remaining pair inequality follows from the bound on D.
* For (1,5,1) the bounds are U+W+D≥a, V+D≥b, V+W≤s, U+V≤t'. Combining U+W+2V≤s+t' proves D≥ceil((a+2b−s−t')/3). The smallest W=a−D−t'+(b−D), derived using U≤t'−V; equality forces V=b−D and U=a−D−W. The remaining upper bound follows from the bound on D.
* For (4,4,2) the bounds are U+V+D≥a, W+D≥b, V+W≤s, U+W≤t'. Thus D≥ceil((a+2b−s−t')/3). Choose smallest W=b−D, then V=a−D−t'+W and U=a−D−V; the remaining upper bound again follows.
* For (5,1,1) the bounds are V+W+D≥a, U+D≥b, U+W≤s, U+V≤t'. Thus D≥ceil((a+2b−s−t')/3). Smallest W=a−D−t'+(b−D); equality forces U=b−D and V=a−D−W; the remaining bound follows.
* For the other three centers, three singleton lower bounds U+D≥a, V+D≥b, W+D≥c combine with total U+V+W≤s to give D≥ceil((a+b+c−s)/3). Taking all three at their lower limits simultaneously attains the lex minimum.

These formulas optimize over all integer offsets, so no arbitrary numerical offset cutoff is used. Every resulting optimum is a fixed offset for that residue and hence qualifies for the eventual collision analysis. Compare the seven minima by full lex order of digits: for large t this is exactly comparing (G,c,F,b,E,a,A). Substitution gives the stated six rows, reproducible with the short accompanying [carry replay](replay/erdos232_six_residue_replay.py) (the Python standard library suffices). Actual mex is in some bounded-offset center by the geometry, and the displayed candidate is a genuine admissible digit tuple for large t, so the comparison proves exact equality.

Expanding yields the following coefficients after the common h⁴/3 term:
| r | h³ | h² | h | constant |
|---|---:|---:|---:|---:|
| 0 | 5/6 | 4/3 | 7/6 | 1 |
| 1 | 5/6 | 7/6 | 7/6 | 3/2 |
| 2 | 2/3 | 5/3 | 1 | 2/3 |
| 3 | 7/6 | 5/6 | 3/2 | 1/2 |
| 4 | 1 | 1 | 4/3 | 4/3 |
| 5 | 1 | 1 | 4/3 | 1 |

The minimal eventual quasiperiod is six: r=0 and r=2 have distinct cubic coefficients, as do r=0 and r=3, excluding divisors two and three. Any alternative eventual period induces its gcd with six by equality of polynomials on each infinite intersection of compatible arithmetic progressions, so no smaller or incompatible period bypasses this check.
