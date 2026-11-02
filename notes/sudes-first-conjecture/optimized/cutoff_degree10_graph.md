# A degree-10 graph with the required half-capacity cuts

This additive refinement of [G1](cutoff_graph_experiment.md) changes a finite graph construction and imports no
additional analytic theorem.

For every n at least two there is an undirected multigraph on n vertices,
with maximum degree at most ten and


```math
|\partial S|\ge\frac12\min(|S|,n-|S|)            \qquad\text{(G10.1)}
```


for every vertex set S. Edge multiplicities are retained and loops discarded.
For n at most seven use the complete graph, whose maximum degree is at most
six and whose cut has s(n-s) edges. Now suppose n at least eight.

Choose five independent uniform permutations. For a fixed set S of s at
most n/2 vertices write t=s/n. If fewer than s/4 directed permutation edges
leave S, more than 19s/4 of its 5s images stay inside S. In particular,
some k=ceil(19s/4) specified images stay. For any such specification the
probability is at most t to the power k: the falling-factorial probability
within each permutation is at most the corresponding power of t, and the
five permutations are independent.

The number of specifications is at most exp(5s H(1/20)), where H is binary
entropy with natural logarithms. Rounding k upward only decreases the
entropy and strengthens the probability bound. As there are at most
(en/s) to the power s possible sets S, the union bound at size s is at most


```math
\{\exp(1+5H(1/20))t^{15/4}\}^{s}.             \qquad\text{(G10.2)}
```


Put r=exp(1+5H(1/20))2 to the power -15/4. The exact comparison is


```math
r^4=\exp(4)\frac{20^{20}}{19^{19}2^{15}}
 \lt \left(\frac{11}{4}\right)^4
       \frac{20^{20}}{19^{19}2^{15}}
 \lt \left(\frac35\right)^4.                     \qquad\text{(G10.3)}
```


The elementary bound exp(1)<11/4 is proved in G1; the last comparison is
between explicit integers. The former single-ratio test r<1/2 is unnecessary.
For s at most n/4, t at most 1/4 improves the ratio in (G10.2) to at most
r/2 to the power 15/4, strictly less than (3/5)/8=3/40. For s>n/4 and
n at least eight we have s at least three, and the ratio is at most r<3/5.
The total bad-event probability is therefore strictly less than


```math
\sum_{s\ge1}(3/40)^s+\sum_{s\ge3}(3/5)^s
 =\frac3{37}+\frac{27}{50}\lt 1.                 \qquad\text{(G10.4)}
```


Some tuple of permutations avoids every bad set. In each permutation the
incoming and outgoing cut counts agree, so the undirected multigraph cut
has twice the outgoing count. This proves (G10.1), including every n.
Finite enumeration of permutation tuples and all cuts is a terminating
construction specification; no efficient algorithm is claimed.

For a controller reservoir capacity C=floor(KX/g), any integral demand
coordinate of absolute value at most KX/(2g) is at most
floor(KX/(2g))=floor(C/2). Its cut sum is bounded by C/2 times the smaller
side of the cut, at most C times the edge boundary by (G10.1). Integral
max-flow/min-cut therefore realizes the full required zero-sum demand box,
with integer capacity C on each edge. Edge multiplicities are separate
reservoirs; they are not collapsed into a simple graph.

Each graph has at most 5n edges. The row and column networks together have
at most 10n ordinary reservoirs, and their entry coefficient is 20n.
Both diagonal reservoirs and every residue gadget remain separate. This
refinement does not authorize sharing entry positions or reservoir primes.

The accompanying
[cutoff_degree10_graph.py](../PROVENANCE.md#optimized-bound) verifies the
exact rational comparisons, small complete-graph controls, and all cuts in
deterministic sample constructions. A repeated cycle satisfies the degree
bound but fails the required expansion and is an intended negative control.
These finite checks do not independently prove the universal probabilistic
construction; (G10.2)--(G10.4) are the conventional proof of its whole tail.

[Manuscript index](../README.md) · [Optimized theorem](../optimized-bound.md) · [Source and review record](../PROVENANCE.md#optimized-bound)
