# Exact proof of the six-residue formula for all positive orders

This proves the [stated formula](README.md), with a symbolic calculation for
$h\ge60$ and a finite prefix check. Let $h=6k+r$, with $0\le r<6$, and set
$H=h+1$, $B=h^2+h+1$, $K=\lfloor(h+3)/2\rfloor$ and $R=\lfloor h/2\rfloor$.
The fourth positive term is
$C=KB-(K-1)H+R$, by [O'Bryant, Lemma 2.4](https://arxiv.org/html/2312.10910v3).
The proposed coefficients $(c,q,s,t)$ are the six rows in the main note.

## The exact carry predicate

An integer x>C is forbidden precisely when $mx=c_1C+bB+aH+d$ for some $1\le m\le h$, where the signed vector (c₁,b,a,d) has sum of positive entries ≤h and sum of absolute negative entries at most $h-m$; this is an actual pair of equal h-sums, padded by zeros. Necessity cancels common terms. In particular $mx\le hC$. In the window $c:=\lfloor x/C\rfloor\ge R+1$ only $m=1$ is possible.

Successive Euclidean bases C,B,H give the unique canonical tuple (c,q,s,t). The non-leading bounds are 0≤q≤K−1, 0≤s,t≤h, with s=h implying t=0, and if q=K−1 one additionally needs either s<H−K or s=H−K,t≤R. These follow from B=hH+1 and C−(K−1)B=(H−K)H+R+1. Lexicographic order of canonical digit tuples gives integer order.

In an $m=1$ collision let j=c₁−c and l=b−q+jK. Then exactly
    c₁=c+j, b=q−jK+l, a=s+j(K−1)−lh+z, d=t−jR−l−zH
for an integer z. Conversely these formulas always evaluate to x. Every actual relation is captured by |j|≤3, |l|≤4, |z|≤4 for h≥60, because |c₁|,|b|,|a|,|d|≤h and
    |j|C < C+h(B+H+1) < 4C,
    |l|B ≤ (2h+3(K−1))H+2h+3R < 4B,
    |z|H ≤ 2h+3R+4 < 4H.
The inequalities use C≥h³/2, K−1≤(h+1)/2, and R≤h/2. The constants are deliberately rounded outward. At c≥R+1 we have c₁>0; thus the two signed bounds are imposed by requiring c₁+Σ_U v≤h and −Σ_U v≤h−1 for every subset U of v=(a,b,d). For each fixed carry triple these are linear in k and trial digits. Their finite disjunction is exactly the forbidden predicate in the window.

## Computed exact integer obligations

For each residue class the 18 independent UNSAT results (three per class) certify:
1. No k≥10 makes the proposed tuple noncanonical or places it outside R+1≤c≤h.
2. No k≥10 yields a forbidden witness at the proposed tuple.
3. No k≥10 admits a strictly earlier lexicographic canonical tuple with R+1≤c≤h which is not forbidden.

The Z3 solver checks all integer k≥10 at once. The input contains exclusively linear integer constraints and logic; no floating point, random sampling, or bound on k.

## Why the discarded low window cannot conceal the true mex

For every k≥10 the proposed first digit c exceeds R+1, directly from the six rows. Consequently obligation 3 proves that every canonical residual (q,s,t) occurs in an $m=1$ forbidden relation with $c=R+1$. For any 4≤c<R+1, take that very relation and lower only the coefficient c₁ by R+1−c. The new coefficient is c+j≥1 since j≥−3; the positive budget only decreases, the negative budget remains unchanged, and the represented x decreases as desired. Thus all these lower trials are truly forbidden as well.

When 0≤c≤3, any x<C·4 is below γ₅(h) by O'Bryant's Theorem 1.2, γ₅(h)≥h⁴/8+h³/2. Indeed C≤(h+3)h²/2+(3h+2)/2; for h≥60 this lower bound is strictly above 4C. Hence obligations 1–3 certify the global mex for h≥60. The finite range below 60 is handled separately below.

## The small orders

Proof of exact checker: its candidate interval [L,U] starts at the larger of C+1 and ceil(h³(h+4)/8) by O'Bryant's lower bound, and ends at hC+1. Only positive r≤h with rL≤hC matter. Enumerate all signed c,b,a recursively while paying their positive budget by h and their negative budget by h−r. The permitted last coefficient d is every integer in [−N,P], where N,P are the unspent negative/positive budgets. Thus the integer trial x is forbidden by this r,c,b,a precisely when r x lies in [cC+bB+aH−N,cC+bB+aH+P]. This is a whole clipped integer interval in x, with exact inclusive bounds by ceiling/floor division. The difference array unions the literal intervals; the first x with zero coverage is the true mex by the signed-collision equivalence. All arithmetic fits int32 over this small range. The polynomials are used only for the post-computation assertions.


The actual computation covers all $1\le h<60$. The formula has just one
exception: at $h=4$ it predicts 172, while the true greedy term is 153.
This finite argument uses O'Bryant's Theorem 1.2 to start the candidate
interval; the alternate coefficient replay enumerates the complete
forbidden range starting at $C+1$, without that lower bound.

## Least eventual period

Substitution into the digit formula gives the $h^3$ coefficient $5/6$
when $h\equiv0\pmod6$, $2/3$ when $h\equiv2\pmod6$, and $7/6$ when
$h\equiv3\pmod6$. This excludes periods two and three, as well as one.
If a second eventual period exists, agreement of polynomials on the
infinite intersections of compatible progressions makes its gcd with six
an eventual period. Consequently the least eventual quasiperiod is six.

## Replay

Run these commands from this directory. Use Python 3, C++17, and the Z3 shared
library `libz3.so.4` for the first command. The Python generator can also emit
SMT-LIB for separate testing with another solver. No formal proof trace is
included.

```sh
python3 replay/check_native_0232_period_six.py
python3 replay/check_native_0232_period_six.py --emit 3 improve > query.smt2
g++ -std=c++17 -O3 replay/check_native_0232_small_interval.cpp -o /tmp/greedy-interval
/tmp/greedy-interval
g++ -std=c++17 -O3 replay/check_greedy_bh_gamma5_small.cpp -o /tmp/greedy-coeff
/tmp/greedy-coeff 59
python3 replay/erdos232_six_residue_replay.py
```

The symbolic replay should report `unsat` for all 18 queries. The two finite
enumerations compute the minimum admissible value independently and use
the residue formula for comparison. The last program replays the
bounded-offset carry optimization used by the solver-free eventual proof.

**Reference.** Kevin O'Bryant, [*Bounds for Greedy Bₕ-Sets*](https://arxiv.org/html/2312.10910v3),
Theorem 1.2, Lemma 2.4, and §3; *Electronic Journal of Combinatorics* **32**
(2025), #P2.39.
