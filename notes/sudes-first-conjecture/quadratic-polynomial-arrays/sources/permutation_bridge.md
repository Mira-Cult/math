# Exact permutation geometry and a local-lemma bridge

The models are fixed in [PROBLEM.md](../README.md#exact-pool-and-geometry). This manuscript supplies
the probability interface used by [Theorem Q2](characteristic_zero.md), with
all dependencies of a uniform permutation retained. Labels below are local
to this manuscript; no permanent claim identifiers have been allocated.

## Geometry

For order n at least two and dimension D, choose a nonempty varying-coordinate
set J, assign signs to its coordinates modulo simultaneous reversal, and fix
the other coordinates arbitrarily. There are


```math
L_D(n)=\sum_{j=1}^{D}\binom Dj 2^{j-1}n^{D-j}
       =\frac{(n+2)^D-n^D}{2}
```


distinct lines. The varying set and fixed coordinates are recovered from the
cell set, and the varying signs are recovered up to common reversal. Thus
there is no overcount, including n=2. At n=1 all descriptions give one cell.
For n=2, any two different cells form exactly one such line.

Every cell is on at most


```math
r_D:=\sum_{j=1}^{D}\binom Dj2^{j-1}=\frac{3^D-1}{2}
```


lines: for each direction pattern a cell determines at most one line.
In particular n L_D(n) <= n^D r_D by counting incidences. Two distinct
full lines share at most one cell, because they are straight real affine
lines and two points determine one affine line. No independence conclusion
is drawn from disjointness of cell sets in a random bijection.

## The elementary union bound

Let A be any pool of N=n^D distinct entries and let B be a family of bad
n-element subsets. For polynomial arrays, membership in B means that the
sum fails the relevant irreducibility/content condition. Put


```math
b=\frac{|B|}{\binom Nn}.
```


A uniform bijection from cells to A gives each line a uniform n-subset.
The union bound therefore proves existence if L_D(n)b<1. This requires no
independence. It proves neither a useful bound on b nor its sharpness.

For the stronger interface define


```math
\beta_a=\Pr(S\in B\mid a\in S),\qquad
 \beta=\max_{a\in A}\beta_a,
```


where S is a uniform n-subset. Double counting gives
b=N^{-1}\sum_a\beta_a, and consequently b<=beta. A bound on b alone does
not automatically bound every beta_a.

## Permutation theorem

Here $`(N)_n=N(N-1)\cdots(N-n+1)`$ denotes the falling factorial.

**Theorem PL.** Let V and A have the same finite size N, and let H be an
n-uniform hypergraph on V, where 2<=n<=N. Suppose every vertex of H is on
at most Delta edges. For a fixed family B of bad n-subsets of A, define
beta as above. If


```math
8n\Delta\beta\le1,                                    \qquad\text{(PL)}
```


and (N)_n>2, some bijection V -> A maps no edge into B.
For the signed-line problem it is sufficient that


```math
8n r_D\beta\le1.                                     \qquad\text{(SL)}
```


**Proof.** Work in the uniform space of bijections V -> A. For each edge
L of H, each bad subset S, and each bijection f:L -> S, introduce the
canonical event E_f that the random bijection extends f. Its probability is


```math
p_0=\frac1{(N)_n}.
```


The graph joining two canonical events when their partial bijections
conflict is a negative dependency graph, by Lu--Szekely, Theorem 1, with
|V|=|A| (their injection theorem includes bijections). A conflict means
different images of one shared domain element or different preimages of
one shared range element. In particular a conflict requires overlapping
domains or overlapping ranges. The larger graph connecting any such
overlap is still a negative dependency graph: its allowed sets of
nonneighbors are subsets of those allowed for the original graph.

Fix E_f with domain L and range S. Bound the sum of probabilities of all
neighboring canonical events, allowing overcount and inclusion of E_f.
For a fixed hyperedge L', the sum over all its bad canonical assignments
is b, since those assignments are disjoint. Hence the domain-overlap
contribution is at most


```math
\sum_{v\in L}\sum_{L'\ni v} b\le n\Delta b.
```


For a fixed a in A and a fixed L', the sum over bad canonical assignments
whose range contains a equals


```math
\Pr(\text{range on }L'\text{ is bad and contains }a)
       =\frac nN\beta_a.
```


The range-overlap contribution is consequently at most
n |H| (n/N) beta. Since n|H|<=N Delta, the total is at most


```math
n\Delta b+n\Delta\beta\le2n\Delta\beta.              \qquad\text{(1)}
```


Assign x_f=2p_0<1 to every event. Equation (1) and (PL) imply
sum_{g neighbor f} x_g <=4n Delta beta <=1/2. For finitely many numbers
in [0,1], product(1-x_g)>=1-sum x_g; therefore


```math
x_f\prod_{g\sim f}(1-x_g)\ge2p_0(1/2)=p_0.
```


The negative-dependency version of the local lemma (Lu--Szekely, Lemma 3)
gives positive probability that none of the canonical events occurs. This
is exactly a bijection avoiding every bad line subset. QED.

The use of canonical events is essential: the ordinary bad-line events
are not claimed independent when their cell sets are disjoint. Both kinds
of conflict, including the shared-entry conflict, are paid in (1).

## Consequences for the quadratic bound

[The quadratic manuscript](characteristic_zero.md) proves, for the exact
degree-two prefix and each fixed D>=2, a uniform one-entry-conditioned bound


```math
\beta\le 2^{104}(D+3)(\log n)^2 n^{-D/3-1/2}+n^{-10}
```


in its explicit range. With N_Q(2,D)=2^{1024(D+1)}, its whole-tail
calculation establishes (SL), hence Theorem Q2. The degree, representatives
and exact final partial shell are unchanged. No rescaling or extra entry
is introduced by the local lemma.

For comparison, plugging this estimate into the elementary union bound
gives an upper bound of order n^{2D/3-3/2}(log n)^2. That decreases for
squares but not for cubes. This does **not** prove that the true cube union
bound fails; it identifies the insufficiency of this particular upper
estimate. The permutation theorem needs only n beta to be small, and that
decreases for every fixed D>=2.

All existence conclusions have a finite effective construction by exhaustive
enumeration of permutations and exact checking. The proof does not establish
a practical running time or an efficient resampling algorithm. The number
of canonical bad events is finite but very large.

## Source

Linyuan Lu and Laszlo A. Szekely, *Using Lovasz Local Lemma in the Space of
Random Injections*, Electronic Journal of Combinatorics 14(1) (2007), R63,
Theorem 1 and Lemma 3, printed pages 2--4. The author's PDF is
[randinj.pdf](https://people.math.sc.edu/lu/papers/randinj.pdf); the
[journal record](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v14i1r63)
fixes volume 14. The author's PDF footer says 13, a bibliographic typo.
No independence statement for arbitrary polynomial-sum events is imported.

