# Prime line sums: problem statement

## Statement

For each positive odd integer $n$, put $N=n^2$ and
$P_n=\{p_2,p_3,\ldots,p_{N+1}\}$, where $p_j$ is the $j$-th rational prime,
including $p_1=2$. Does there exist $n_0$ such that every odd $n\ge n_0$
admits a bijection from the cells of an $n\times n$ square to $P_n$, for
which every row, every column, and both main diagonal sums is prime?

## Goals

Prove eventual existence, or produce a rigorous unbounded family of failing odd
orders. A theorem for an unbounded successful subsequence is a lesser intermediate
result. Finite certificates, conditional implications, imported theorems,
heuristics and conjectures remain distinguished.

Principal proof tracks are constructive designs and repairs, structured
composite-divisor covers, polynomial/counting identities, and a source-faithful
attempt to transport the count to the quadratic/sextic estimates in the pinned
quasi-RH source. The analytic obligation includes all growing-parameter losses.

## Model and scope

The labelled cells are $V=\{0,\ldots,n-1\}^2$. The labelled required line
family $\mathcal L$ consists of $n$ rows, $n$ columns, the main diagonal
and the antidiagonal. For $n=1$ these four labels denote the same singleton;
the trivial witness is $[3]$. For $n\ge3$, there are $2n+2$ distinct lines.
Let $S_L(\sigma)=\sum_{v\in L}\sigma(v)$, and let $Z_n$ count successful
labelled bijections $\sigma:V\to P_n$. Equal line sums and equality of a line
sum with a pool entry are allowed. Every pool entry is used exactly once.

Let $V_n$ and $U_n$ be respectively the sums of the $n$ smallest and $n$
largest elements of $P_n$; all line sums lie in $[V_n,U_n]$.
For a rational prime $q\le\sqrt{U_n}$, the bad event is
$B_{L,q}=\{\sigma:q\mid S_L(\sigma),\ S_L(\sigma)>q\}$.
The strict inequality is part of the definition, not an approximation.
The total pool sum is $T_n=\sum_{p\in P_n}p$.

No extra primes, replacement pool, unspecified starting block, equal magic
constant or distinct-sum requirement is admitted. Even $n\ge2$ is impossible
because each line sum is even and greater than 2. Arbitrary prime-entry squares
are explicitly labelled relaxed controls.

Computational certificates contain `n`, the ascending `pool`, a flat row-major
`permutation` of actual values, and `line_sums` with `rows`, `columns`,
and `diagonals` (main, antidiagonal). Optional search metadata never replaces
independent recomputation.
