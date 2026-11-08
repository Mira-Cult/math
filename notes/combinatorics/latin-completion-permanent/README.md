# Partial Latin square completions as one exact permanent

**Status:** a complete conventional proof and an executable exact-arithmetic
construction, with finite checks. No formal verification, external referee
acceptance, novelty, or minimality claim is made. See [verification](VERIFICATION.md).

For every partial Latin square, this note constructs one matrix over
$\{-1,0,\tfrac12,1\}$ whose permanent is exactly the number of completions.
There is no multiplier outside the permanent and no interpolation.
After elementary forced-cell propagation, a residual instance with $h$ holes
and $t$ allowed cell-symbol choices gives a matrix of order $t+2h$ with exactly
$5t+h$ nonzero entries. Constant outcomes are handled separately.

The proof uses a signed cyclic block whose unused permanent vanishes and whose
one-input/one-output response is twice the identity. Counting the external
rows forces every nonvanishing group of terms to use each cell block once.
A diagonal block of halves supplies the exact normalization.

## 1. Statement and input conventions

Rows, columns and symbols are labeled. A completion of an order-$n$ partial
Latin square is an $n\times n$ array over $[n]=\{1,\ldots,n\}$ that extends its
clues and contains each symbol once in every row and every column. Let
$C(P)$ be the number of completions. We allow an input array with contradictory
clues and set its count to zero. Assume $n\geq1$.

For a square matrix $X$ of order $d$, write

$$
\operatorname{per}(X)=\sum_{\sigma\in S_d}\prod_{r=1}^d X_{r,\sigma(r)},
\qquad \operatorname{per}(\varnothing)=1.
$$

**Theorem.** There is a deterministic construction, polynomial-time in an
explicitly supplied grid, of a matrix $M_P$ over
$\{-1,0,\tfrac12,1\}$ satisfying

$$
\boxed{\operatorname{per}(M_P)=C(P).}
$$

The construction first validates the clues, checks empty requirements, and
repeatedly fills a cell that has exactly one allowed symbol. If a contradiction
is detected it returns $[0]$. If the grid becomes complete it returns $[1]$.
Otherwise, let $h$ and $t$ be the numbers of holes and allowed cell-symbol
choices **after** this preprocessing. Then

$$
\boxed{\dim M_P=t+2h,\qquad \operatorname{nnz}(M_P)=5t+h.}
$$

Here every residual hole has at least two allowed symbols, so $t\geq2h$.
In all cases, the matrix order is at most $n^3+2n^2$ and the number of nonzeros
is at most $5n^3+n^2$.

A sparse list of the residual matrix's nonzero coordinates and constant
weights has $O((t+h)\log(t+h+2))$ bits. This excludes the optional forced-cell
history and original-grid labels emitted by the example program. A dense
serialization instead has
$(t+2h)^2$ entries. These are output bounds, not a promise of running time
polynomial in a sparse clue list when $n$ itself is supplied in binary.

## 2. Residual requirements and forced cells

For a hole $c=(i,j)$ define its candidate set

$$
K_c=[n]\setminus\bigl(\{\text{clues in row }i\}\cup
                              \{\text{clues in column }j\}\bigr).
$$

The residual requirements are:

1. one symbol in each hole $(i,j)$;
2. one occurrence of each symbol $k$ missing from row $i$, denoted $R(i,k)$;
3. one occurrence of each symbol $k$ missing from column $j$, denoted $C(j,k)$.

A candidate $(i,j,k)$, with $k\in K_{(i,j)}$, meets these three requirements.
If the clues contain no row or column repetition and there are $h$ holes,
there are exactly $h$ requirements of each kind. Indeed, a row with $r$ holes
has $n-r$ distinct clues and therefore exactly $r$ missing symbols; sum over
rows, and similarly over columns. Write

$$
t=\sum_{c\text{ a hole}}|K_c|.
$$

If **any** of the three kinds of requirement has no candidate, the completion
count is zero. This includes a missing row-symbol or column-symbol even when
every cell has a nonempty candidate set.

If a cell has $K_{(i,j)}=\{k\}$, every completion must put $k$ there. Filling
that cell gives a bijection on completions: restriction forgets the newly
recorded clue and extension restores its forced value. Recompute the
requirements after filling it, and continue. The executable construction uses
one cell at a time in lexicographic order. Consequently simultaneous
incompatible forced choices are never silently accepted; a later recomputation
detects the resulting obstruction. At most $n^2$ cells can be filled.

It is enough to propagate singleton **cell** requirements. Singleton
row-symbol or column-symbol requirements need not be propagated for this proof.
At termination, either a zero case was detected, a validated complete square
has count one, or every remaining cell has at least two candidates. The
preprocessing is not a complete feasibility test: an impossible instance can
reach the residual construction and correctly produce permanent zero.

## 3. The signed cyclic identity

For $q\geq1$, let $P_q$ have entries

$$
(P_q)_{a,a+1}=1\quad(1\leq a<q),\qquad (P_q)_{q,1}=-1,
$$

and zero elsewhere. In particular $P_1=[-1]$. Set

$$
D_q=I_q+P_q,\qquad B_q=I_q-P_q.
$$

Define the **transposed permanental-cofactor matrix** by

$$
(H_q)_{s,u}
=\operatorname{per}\bigl(D_q[\text{delete row }u,\text{ delete column }s]\bigr).
$$

The order of these indices matters: the first index is the deleted column.

**Lemma.** For every $q\geq1$,

$$
\operatorname{per}(D_q)=0,\qquad
H_q=\sum_{\ell=0}^{q-1}P_q^\ell,\qquad
B_qH_q=2I_q.
$$

**Proof.** If $q\geq2$, a nonzero permutation term in $D_q$ must use either
all diagonal entries or the entire directed cycle. Once one row uses its
successor column, the next row cannot use its diagonal, and this forces the
whole cycle. The two terms have weights $1$ and $-1$, respectively, so they
cancel.

For the cofactor, view an allowed matrix entry as an arc from its row label
to its column label. Deleting row $u$ and column $s$ leaves one directed path
from $s$ to $u$, with loops on vertices outside that path. If $s=u$, the path
has length zero and all remaining vertices use loops. If $s\ne u$, its arcs
are forced to follow the signed cycle forward until reaching $u$; it has the
unique length $\ell\in\{1,\ldots,q-1\}$ with $s+\ell\equiv u\pmod q$.
There is no other nontrivial directed cycle because the only such cycle uses
all $q$ vertices. Thus the cofactor has one nonzero permutation term, of weight
$(P_q^\ell)_{s,u}$, proving the formula for $H_q$.

Every $q$ steps around the cycle include its unique negative edge, so
$P_q^q=-I_q$. Hence ordinary matrix multiplication gives

$$
(I_q-P_q)(I_q+P_q+\cdots+P_q^{q-1})=I_q-P_q^q=2I_q.
$$

For $q=1$, the formulas read $D_1=[0]$, $B_1=[2]$, and $H_1=[1]$, using the
empty-permanent convention. All identities still hold. This case explains why
singleton propagation is required for the stated four-value alphabet: an
unprocessed singleton would introduce the entry $2$. $\square$

For example,

$$
D_2=\begin{pmatrix}1&1\\-1&1\end{pmatrix},\quad
B_2=\begin{pmatrix}1&-1\\1&1\end{pmatrix},\quad
H_2=\begin{pmatrix}1&1\\-1&1\end{pmatrix},\quad B_2H_2=2I_2.
$$

## 4. Every entry of the matrix

Work with a nonterminal residual grid. List each cell's candidates in increasing
symbol order:

$$
K_c=(k_{c,1},\ldots,k_{c,q_c}),\qquad q_c\geq2,
\qquad\sum_c q_c=t.
$$

First construct a matrix $A$ of order $h+t$.
Its rows are:

- one external row $R(i,k)$ for each missing row-symbol;
- $q_c$ internal rows $U(c,1),\ldots,U(c,q_c)$ for each hole $c$.

Its columns are:

- one external column $C(j,k)$ for each missing column-symbol;
- $q_c$ internal columns $V(c,1),\ldots,V(c,q_c)$ for each hole $c$.

Use any fixed deterministic order, such as lexicographic order, within these
lists. For each hole $c=(i,j)$, prescribe

$$
\begin{aligned}
 A_{U(c,a),V(c,b)}&=(D_{q_c})_{a,b},\\
 A_{R(i,k_{c,a}),V(c,b)}&=(B_{q_c})_{a,b},\\
 A_{U(c,a),C(j,k_{c,a})}&=1.
\end{aligned}
$$

All unspecified entries are zero. In particular there are no
external-to-external entries, no internal connections between different cells,
and no connections to any other row-symbol or column-symbol slot. The
prescriptions do not overlap: each internal block belongs to one cell, and
its candidate symbols are distinct.

Finally, set

$$
\boxed{M_P=A\oplus\tfrac12 I_h.}
$$

This block-diagonal definition includes zeros in all off-block positions.
It does not construct a fully nonzero matrix.

## 5. Proof of the counting identity

We prove

$$
\operatorname{per}(A)=2^h C(P).
$$

Here and below $P$ can denote the residual grid because preprocessing preserves
its count.

### 5.1 Why exactly one input enters each cell block

Expand the permanent and first group terms by all edges incident to external
rows or external columns. In any such term, let $a_c$ be the number of external
rows entering cell $c$'s internal columns, and $b_c$ the number of internal
rows of that cell exiting to external columns. The remaining internal rows and
columns must match inside that same block, so

$$
q_c-b_c=q_c-a_c,\qquad\text{and therefore }a_c=b_c.
$$

If $a_c=b_c=0$, summing the internal permutations of this block contributes
$\operatorname{per}(D_{q_c})=0$. The entire group cancels. Thus only groups
with $a_c\geq1$ for every cell can have nonzero total weight.

There are exactly $h$ external rows. None can bypass the cell blocks, and
there are exactly $h$ cell blocks. Consequently

$$
\sum_c a_c=h,\qquad a_c\geq1\text{ for all }c
\quad\Longrightarrow\quad a_c=b_c=1\text{ for all }c.
$$

This is a cancellation statement about **sums of terms**. Individual perfect
matchings can leave a block unused or enter another block several times; it
would be incorrect to rule those matchings out one by one.

### 5.2 Why the input and output symbols agree

Now group the remaining terms by which external row and which external column
are assigned to each cell. Suppose cell $c=(i,j)$ receives row
$R(i,k_{c,a})$ and supplies column $C(j,k_{c,u})$.
The output edge uses internal row $u$ and has weight one. If the input edge
uses internal column $s$, its weight is $(B_{q_c})_{a,s}$, and the remaining
internal matchings have total weight $(H_{q_c})_{s,u}$. Summing over $s$ gives

$$
\sum_{s=1}^{q_c}(B_{q_c})_{a,s}(H_{q_c})_{s,u}
=(B_{q_c}H_{q_c})_{a,u}=2\,\mathbf 1_{a=u}.
$$

After the external assignments have been fixed, these sums are independent
between cells: the internal blocks have disjoint rows and columns. Hence
mismatched input/output symbols contribute zero. Each consistent assignment
of symbols to all cells contributes precisely $2^h$.

### 5.3 The surviving assignments are exactly completions

Each hole has one chosen candidate. Every external row $R(i,k)$ is used once,
so every symbol missing from row $i$ is inserted once there. Every external
column $C(j,k)$ is used once, giving the corresponding column condition.
Candidates already exclude conflict with clues. The resulting array is
therefore a Latin completion.

Conversely, a completion specifies for each hole its candidate label and hence
exactly one assignment of its external row and column slots. The local weighted
sum for this assignment is two at every cell. This proves
$\operatorname{per}(A)=2^h C(P)$ without asserting a bijection between individual
permutation terms and completions.

A permutation contributing to the permanent of a block-diagonal matrix must
stay within each diagonal block, so permanents multiply over those blocks.
Thus

$$
\operatorname{per}(M_P)
=\operatorname{per}(A)\operatorname{per}(\tfrac12 I_h)
=2^h C(P)\,2^{-h}=C(P).
$$

The separate matrices $[0]$ and $[1]$ establish the terminal cases. $\square$

## 6. Exact size and alphabet

For $q\geq2$, the diagonal and cycle positions are distinct. The block $D_q$
has $2q$ nonzeros, the input connections $B_q$ have $2q$, and the output
connections have $q$. Different cells cannot collide in these counts.
Summing over cells gives $5t$ nonzeros in $A$; the normalization adds $h$.
There are $h+t$ rows before normalization and $h$ new rows afterward.

More precisely, each cell has $2q-1$ positive entries and one negative entry
inside $D_q$; it has $q+1$ positive entries and $q-1$ negative entries in its
input connections; and it has $q$ positive output entries. Therefore $M_P$ has

$$
4t\text{ entries equal to }1,\qquad
t\text{ entries equal to }-1,\qquad
h\text{ entries equal to }\tfrac12.
$$

All remaining entries are zero. In particular this is an exact small-alphabet
construction, with no large integers or instance-dependent rational weights.

The compiler recomputes finite candidate sets, propagates at most $n^2$ cells,
and writes these entries. Every step takes polynomial time in an explicit grid.
Since $h\leq n^2$ and $t\leq nh\leq n^3$, the stated global bounds follow.
The construction does not evaluate a permanent or count completions while
building the matrix.

## 7. Examples and executable checks

The code uses symbols **0 through n−1**, rather than the proof's 1 through n,
and `null`/`None` for a hole. Malformed shapes or out-of-range/noninteger symbols
raise `ValueError`; contradictory in-range clues produce the zero matrix.

For the empty order-two square, $h=4$, $t=8$, the matrix has order $16$ and
$44$ nonzeros. Its permanent is $2$, the number of labeled order-two Latin
squares. Every cell uses the displayed $q=2$ block.

For the order-three grid

```
0 1 2
. . .
. . .
```

there are two completions, $h=6$, and $t=12$. The construction gives order $24$
and $66$ nonzeros, with permanent $2$.

The grid

```
0 .
. 1
```

has consistent clues but no completion: each off-diagonal cell has no candidate.
It is returned as $[0]$. A complete valid grid, or an order-one hole after its
forced fill, is returned as $[1]$.

For the empty order-$n$ grid with $n\geq2$, no propagation takes place and
$h=n^2$, $t=n^3$. Thus the same theorem represents the total labeled Latin-square
count as a permanent of order $n^3+2n^2$. This is not a claim that this order is
smallest, even for this special case.

Run the reproducible tests with the Python standard library:

```sh
python3 notes/combinatorics/latin-completion-permanent/verify.py
```

To generate the exact sparse matrix for an input JSON file:

```sh
python3 notes/combinatorics/latin-completion-permanent/construct.py input.json
```

The output lists zero-based row/column coordinates and weights as strings
(`"1/2"`, `"1"`, or `"-1"`). Omitted coordinates are zero. The metadata records
the forced cells, residual parameters, external labels, and block offsets.
See [construct.py](construct.py), [verify.py](verify.py), and
[verification.json](verification.json). The tests use an independent enumeration
of Latin squares by row permutations and generic permanent algorithms, rather
than obtaining the expected count by the reduction itself.

## 8. Scope and related literature

Signed weighted permanent reductions are classical. Valiant's permanent
completeness theorem provides the general background [1]. Dell, Husfeldt,
Marx, Taslaman and Wahlén give an explicit linear-size signed-permanent
reduction from counting satisfying assignments [2, Section 3]; together with
a count-preserving Boolean encoding and diagonal normalization, this gives
another route to a constant-alphabet exact representation.

The contribution of this note is the self-contained direct specification and
proof above, with its stated residual size constants and executable checks.
No priority claim for the cyclic gadget or for these constants is made. A
historical novelty audit has not been completed. The direct proof does not
require the SAT reduction, a counting-hardness theorem, or any unproved
complexity separation.

This note does **not** eliminate zero, give an optimal matrix order, or prove
an improved general counting-time bound. Generic permanent evaluation on an
order-$O(n^3)$ matrix does not by itself improve the known elementary
$2^{O(n^2)}$ exact-cover approach to counting Latin completions. For context,
that elementary approach follows directly from inclusion-exclusion: if $U$
is the $3h$ residual requirement set and $T$ the candidate triples, then for
$h\geq1$,

$$
C(P)=\frac1{h!}\sum_{S\subseteq U}(-1)^{3h-|S|}
       \bigl|\{a\in T:a\subseteq S\}\bigr|^h.
$$

The power counts ordered $h$-tuples of triples inside $S$. Inclusion-exclusion
keeps exactly those covering $U$; their $3h$ total incidences must then be
distinct, so they form an exact cover. Each completion has $h!$ orderings.
Enumeration gives a $2^{3h}\operatorname{poly}(n)$ bit-operation bound for an
explicit grid. This observation is only a comparison baseline, not a speedup
claimed for the permanent construction.

### References

1. L. G. Valiant, *The complexity of computing the permanent*, Theoretical
   Computer Science **8** (1979), 189–201.
   [DOI: 10.1016/0304-3975(79)90044-6](https://doi.org/10.1016/0304-3975(79)90044-6).
2. H. Dell, T. Husfeldt, D. Marx, N. Taslaman and M. Wahlén,
   *Exponential Time Complexity of the Permanent and the Tutte Polynomial*,
   ACM Transactions on Algorithms **10**(4) (2014), Article 21.
   [arXiv:1206.1775](https://arxiv.org/abs/1206.1775), especially Section 3.
