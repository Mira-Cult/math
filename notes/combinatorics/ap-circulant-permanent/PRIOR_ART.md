# Relation to bounded weighted width matching algorithms

The direct recurrence in [README.md](README.md) gives a short proof for
arithmetic progression circulants and, more generally,
$`M_{ij}=u_i+v_j+t\mathbf{1}_{j<i}`$. This note explains why polynomial-time
tractability also follows from established weighted matching theory. The
reduction and the explicit same-exponent specialization below are derived
here; they are not statements attributed verbatim to the cited paper.

## 1. The applicable general theorem

Uffe Flarup and Laurent Lyaudet, *On the Expressive Power of Permanents and
Perfect Matchings of Matrices of Bounded Pathwidth/Cliquewidth*, Theory of
Computing Systems **46**(4), 761–791 (2010),
[DOI 10.1007/s00224-009-9241-3](https://doi.org/10.1007/s00224-009-9241-3).
See the [author-hosted journal manuscript](https://lyaudet.eu/laurent/Publi/Journaux/cliquepermTOCS.pdf)
and [2008 preprint](https://arxiv.org/abs/0801.3408).

Theorem 12 constructs polynomial-size arithmetic circuits for the weighted
perfect-matching sum of bounded weighted NLC-width graphs when a construction
expression is supplied. Theorem 1 relates weighted NLC-width and weighted
clique-width, and Theorem 13 gives the corresponding permanent statement.
We use the weighted **perfect-matching** formulation via the explicit graph
below. Arbitrary weights on a complete graph do not meet a bounded weighted
width condition merely because the unweighted support is a clique.

The paper does not state the AP-circulant result, the gadget construction
below, or the direct four-counter recurrence in this package. Those bridges
need to be supplied before applying its general theorem.

## 2. A weight-preserving gadget reduction

For row $`i`$, create a five-vertex path

```math
R_U(i)-x(i)-R_V(i)-y(i)-R_T(i)
```

whose consecutive edge weights are $`(1,u_i,t,1)`$. For column $`j`$, create
a five-vertex path

```math
C_V(j)-a(j)-C_U(j)-b(j)-C_T(j)
```

with edge weights $`(1,v_j,1,1)`$. The three $`R`$ or $`C`$ vertices of each
path are its ports. Add weight-one external edges

```math
\begin{aligned}
R_U(i)&-C_U(j) &&\text{for all }i,j,\\
R_V(i)&-C_V(j) &&\text{for all }i,j,\\
R_T(i)&-C_T(j) &&\text{exactly when }j<i.
\end{aligned}
```

In any perfect matching, the two non-port vertices of a gadget must match
two distinct ports internally. Exactly one port is therefore matched
externally. For each choice of that port the internal matching is unique.
Its row-gadget weight is $`u_i,1,t`$ for ports $`U,V,T`$, respectively;
its column-gadget weight is $`1,v_j,1`$ for ports $`U,V,T`$, respectively.

External edges thus specify a permutation together with a choice of
$`U,V,T`$ for each selected entry. The product of gadget weights is exactly
the corresponding expanded permanent monomial. Conversely, each such
monomial determines a unique perfect matching. The weighted perfect-matching
sum of the $`10n`$-vertex graph is therefore $`\mathrm{per}(M)`$. Zero and
negative weights cause no problem; the argument is a polynomial identity.

## 3. A constant-width construction expression

Use eleven labels: accumulated active labels $`R_U,R_V,C_U,C_V,C_T`$, one
inactive label $`D`$, and five temporary labels $`Q_0,\ldots,Q_4`$.
Process indices in increasing order.

1. Build row $`i`$'s path on five fresh, individually labeled temporary
   vertices. Join its $`U,V,T`$ ports to the accumulated $`C_U,C_V,C_T`$
   labels, respectively, with uniform weight one. Relabel its $`U,V`$ ports
   as $`R_U,R_V`$. Relabel its $`T`$ port and both internal vertices as
   inactive $`D`$.
2. Reuse the five temporary labels for column $`i`$'s path. Join its $`U,V`$
   ports to accumulated $`R_U,R_V`$, respectively, with weight one. Add no
   edge from its $`T`$ port to an old row. Relabel its three ports as
   $`C_U,C_V,C_T`$ and its internal vertices as $`D`$.

No later edge operation touches $`D`$. A row's $`T`$ port can be retired
immediately because future columns are ineligible. Rows are inserted before
the same-index columns, so the $`T`$ edges have precisely the strict
inequality $`j<i`$. All label-pair joins use one uniform weight. The
construction has constant many operations per index and is a valid weighted
clique expression, not just an unweighted support description.

It can also be expressed directly in weighted NLC form with eleven labels:
make each new five-vertex path as a separate right operand, add the specified
edges across the old/new boundary, and then relabel. Consequently there is
no hidden expression-size assumption in applying the weighted theorem.

## 4. The matching framework also gives the same bound

Flarup and Lyaudet's matching method records the number of unmatched vertices
of each label. For this expression, discard any state with an unmatched
inactive vertex, since that vertex can never receive a later edge. The
remaining profile is

```math
(r_U,r_V,c_U,c_V,c_T).
```

The graph is bipartite: all row ports and all column internal vertices lie
on one side, and all column ports and all row internal vertices on the other.
After a complete row-column pair the two sides have equal size. After a row
insertion the first side has one extra vertex. Thus every surviving profile
satisfies, respectively,

```math
r_U+r_V=c_U+c_V+c_T,
\qquad
r_U+r_V=c_U+c_V+c_T+1.
```

Only four counts are independent, so there are $`O(n^4)`$ profiles. For a row
gadget, a surviving matching leaves exactly one port unmatched internally:

- Choose $`U`$, with weight $`u_i`$: leave a new $`R_U`$ vertex unmatched, or
  match one of the $`c_U`$ old $`C_U`$ vertices.
- Choose $`V`$, with weight $`1`$: leave a new $`R_V`$ vertex unmatched, or
  match one of the $`c_V`$ old $`C_V`$ vertices.
- Choose $`T`$, with weight $`t`$: match one of the $`c_T`$ old $`C_T`$
  vertices. It cannot remain unmatched because it becomes inactive.

For a column gadget there are also five possibilities:

- Choose $`U`$, with weight $`1`$: leave a new $`C_U`$ vertex unmatched, or
  match one of the $`r_U`$ old $`R_U`$ vertices.
- Choose $`V`$, with weight $`v_i`$: leave a new $`C_V`$ vertex unmatched, or
  match one of the $`r_V`$ old $`R_V`$ vertices.
- Choose $`T`$, with weight $`1`$: leave a new $`C_T`$ vertex unmatched.
  There is no eligible old row $`T`$ port.

Matching an old label multiplies by its unmatched count. Start with weight
one at the zero profile and return the zero-profile weight after all gadgets.
Every partial matching decomposes uniquely into its previous matching, the
gadget's internal matching, and at most one new external edge. All old
unmatched vertices of one label have identical future weighted neighbors,
so the counts suffice.

There are $`2n`$ stages, $`O(n^4)`$ profiles, and five transitions per profile.
Using four independent indices and rolling arrays gives $`O(n^5)`$ ring
operations and $`O(n^4)`$ stored ring elements. See
[check_profile.py](check_profile.py) for an executable version. Unlike the
direct recurrence, this version completes $`U,V`$ edges chronologically
instead of deferring them to terminal factorials.

The general theorem alone has a much looser off-the-shelf bound: the journal
proof gives $`O(k^2N^{2k+1}\log N)`$ circuit gates per NLC product. Our
$`O(n)`$-length expression with $`N=10n,k=11`$ gives the safe unoptimized
bound $`O(n^{24}\log n)`$. The specialization above removes that overhead.
It would therefore be misleading to advertise the direct recurrence as an
asymptotic improvement over their method by comparing only to the loose
black-box bound.

## 5. Related circulant and permanent literature

- Alexander I. Barvinok, *Two Algorithmic Results for the Traveling Salesman
  Problem*, Mathematics of Operations Research **21**(1), 65–84 (1996).
  [Author manuscript](https://www.math.ucdavis.edu/~deloera/MISC/LA-BIBLIO/trunk/Barvinok/tspalgorithmicold.pdf).
  The fixed-rank permanent theorem is relevant background. It does not
  apply just because our matrix is rank two plus a staircase: the staircase
  alone can have rank $`n-1`$ over a field.
- Mordecai J. Golin, Yiu Cho Leung and Yajun Wang, *Permanents of Circulants:
  a Transfer Matrix Approach*, ANALCO 2006, 263–272,
  [DOI 10.1137/1.9781611972962.11](https://doi.org/10.1137/1.9781611972962.11),
  [expanded version](https://arxiv.org/abs/0708.0907).
  Fixed or linearly moving support jumps differ from AP weights on all
  $`n`$ diagonals. The paper includes weighted variants, but allowing its
  support parameters to grow with $`n`$ does not preserve the advertised
  fixed-parameter recurrence cost.
- Larry J. Cummings and Jennifer Seberry Wallis, *An Algorithm for the
  Permanent of Circulant Matrices*, Canadian Mathematical Bulletin
  **20**(1), 67–70 (1977),
  [DOI 10.4153/CMB-1977-011-3](https://doi.org/10.4153/CMB-1977-011-3).
  Its general circulant method filters $`n^n`$ candidate indexed monomials;
  it is not the polynomial AP evaluation recurrence given here.
- Mustafa Bahsi and Süleyman Solak, *On the Circulant Matrices with
  Arithmetic Sequence*, International Journal of Contemporary Mathematical
  Sciences **5**(25), 1213–1222 (2010),
  [paper](https://www.m-hikari.com/ijcms-2010/25-28-2010/solakIJCMS25-28-2010.pdf).
  This studies the same AP matrix family, with results about eigenvalues,
  determinant, norms and inverse, rather than the permanent recurrence.
- V. V. Kocharovsky, Vl. V. Kocharovsky, V. Martyanov and S. Tarasov,
  *Exact Recursive Calculation of Circulant Permanents: A Band of Different
  Diagonals inside a Uniform Matrix*, Entropy **23** (2021), 1423,
  [DOI 10.3390/e23111423](https://doi.org/10.3390/e23111423),
  [preprint](https://arxiv.org/abs/2109.01740).
  Their explicit linear-time recurrences treat a fixed small band of
  exceptional diagonals on a uniform background. Generic nonconstant AP
  circulants have $`n`$ distinct diagonal weights, a different input family.
- [OEIS A086759](https://oeis.org/A086759) supplies known numerical values
  for the $`A=0,B=1`$ specialization, up to a row permutation. These are a
  numerical baseline, not an attribution for this polynomial algorithm.

This comparison does not establish that the direct recurrence is new, best
possible, or previously unpublished in an equivalent form. The exact
recurrence and its AP specialization are recorded here without a priority
claim. The reduction establishes applicability of known theory; it does not
assert that the original weighted matrix itself has bounded weighted
clique-width.
