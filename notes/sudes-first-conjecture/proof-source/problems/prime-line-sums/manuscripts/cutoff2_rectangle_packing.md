# Exact packing of the independent diagonal rectangles

*Presentation copy: mathematical delimiters and equation labels are adapted for GitHub rendering. The unchanged, hash-bound source is in the [complete replay packet](../../../../packet/README.md).*


Author: /root/controller_redesign. The coordinator independently checked
the compatibility with PB's later ordinary-pair placement. This additive
lemma changes no frozen source. It requires independent nonauthor review
at its exact revision and asserts no numerical square cutoff.

## RP1. A packing at the actual row and column occupancy

Let n be odd and J>=3 be an integer. Suppose n>=2J+1.
For each of J rectangles prescribe either the main or the other main
diagonal. There is a simultaneous placement such that:

* every rectangle has two rows and two columns;
* all2J rows used by the rectangles are distinct, and so are all2J columns;
* each rectangle meets its prescribed diagonal in exactly one cell;
* its other three cells lie on neither main diagonal;
* the center is unused.

The prescriptions may have any multiplicities. In particular this
applies to the equal populations needed for the two diagonal reservoirs.

Index rows and columns by0,...,n-1 and write bar(i)=n-1-i.
Let R={0,...,J-1}. Since n>=2J+1, R is in the first half,
R and bar(R) are disjoint, and neither contains the center.
Use cyclic permutations pi(i)=i+1 modJ and sigma(i)=i+2 modJ
of these labels. Because J>=3,


```math
\pi(i)\ne i,\qquad
                \sigma(i)\notin\{i,\pi(i)\}.               \qquad\text{(RP1)}
```


Choose the designated column


```math
c_i=i\quad\hbox{for a main-diagonal rectangle},\qquad
 c_i=\bar i\quad\hbox{for the other diagonal}.
```


Place rectangle i on the rows and columns


```math
(i,\overline{\pi(i)})\quad\hbox{and}\quad
       (c_i,\overline{c_{\sigma(i)}}).                      \qquad\text{(RP2)}
```


The row set is exactly R union bar(R), with no repetition. The
designated columns select one element of each mirror pair
{i,bar(i)}, and the auxiliary columns select the other elements,
permuted by sigma. The column set is therefore the same disjoint
union, also without repetition.

The designated cell(i,c_i) lies on the prescribed diagonal and not
the other, since i is not the center. For the cell
(i,bar(c_sigma(i))), diagonal membership would force sigma(i)=i.
For (bar(pi(i)),c_i), it would force pi(i)=i.
For (bar(pi(i)),bar(c_sigma(i))), it would force sigma(i)=pi(i).
All three possibilities are excluded by(RP1). This proves the
packing theorem, including both diagonal avoidance and the center.

There is no greedy history, probabilistic assignment, or uncharged
collision condition. The inequality n>=2J+1 pays exactly the
necessary2J distinct rows and columns, with the central index excluded.

## RP2. The rectangle trade does not change

Suppose a rectangle uses rows(i,j), columns(c,k), with(i,c) its
unique diagonal cell. Put two disjoint pairs of common positive gap h
in the array


```math
\begin{pmatrix}
       a & a+h\\
       b+h & b
 \end{pmatrix}.                                           \qquad\text{(RP3)}
```


Switching both horizontal pairs keeps each row sum fixed and changes
the two column contributions by h-h=0 and -h+h=0.
The designated diagonal contribution changes by h; the other diagonal
is unchanged. Reversing the switch changes it by -h. No common lower
residue or equal midpoint is required by this identity.

Different rectangles have disjoint rows and columns, hence disjoint
positions. Their trades are independent. They always permute the
four entries already assigned to them. In a completed prime square,
all other entries remain untouched.

## RP3. Application to the balanced controller

PB places all main and binary-residue rectangles jointly before
placing the ordinary pairs. Its actual total rectangle count is


```math
J_{\rm rect}=4d(P_0+J_b+7K)+2b,\qquad
 P_0\le P,\quad b=\lceil\log_2(g/2)\rceil .                 \qquad\text{(RP4)}
```


The previous greedy sufficient test was n>4J_rect. It can be
replaced by the exact packing test


```math
2\{4d(P+J_b+7K)+2b\}+1\le n.                \qquad\text{(RP5)}
```


All applications have d>=6 and K>=1, so J_rect>=3.
The packing uses the actual count, not fictitious entries for a
prefix that stopped before its cap.

The later PB matching arguments use only these properties of the
rectangles: at most one rectangle in any row or column, at most two
occupied cells there, exactly the prescribed diagonal populations,
and avoidance of the center and unintended diagonal. RP1 supplies
all four. Those arguments do not require the rectangles to have
been produced by the older greedy algorithm.

The per-line common-stage populations, the possible two extra
rectangle cells in an ordinary row or column, the concentration
coefficient3dP+4, and the mean-cancellation formulas are unchanged.
The diagonal amplification remains exactly2d rectangles per main
stage on each diagonal. No entries or positions are reused.

In the existing numerical notation K=floor(n/C), the pointwise
sufficient version of(RP5) is


```math
\frac{8d(P+J_b)}n+\frac{56d}C+\frac{4b+1}n\le1.           \qquad\text{(RP6)}
```


The already required ordinary-placement condition is


```math
\frac{8d(P+J_b)}n+\frac{56d}C+\frac{24b+16}n\lt 1.            \qquad\text{(RP7)}
```


It is stronger than(RP6), since their numerators differ by20b+15>0.
Thus after this explicit packing there is no additional factor-two
rectangle-placement floor. The ordinary matching condition still
has to be verified; this lemma does not weaken or bypass it.

## RP4. Finite controls and proof boundary

The companion checker exhausts every diagonal-type pattern for small
J at the sharp order n=2J+1 and larger odd orders. It checks row and
column uniqueness, all four cells, both diagonals, and the center.
Collision controls deliberately use an insufficient order, pi=id,
sigma=id, sigma=pi, a repeated row, a repeated column and the center.

An actual prime fixture uses precisely the first n² odd primes.
It reserves disjoint equal-gap pairs, fills all remaining positions
with the unused pool, and checks every subset of its rectangle
switches. Every row and column sum remains unchanged, the designated
diagonal increments agree exactly, and the full input permutation
is preserved. The fixture tests the trades; it does not assert that
its baseline line sums are prime.

The universal proof is the elementary construction RP1--RP3.
The finite program is a reproducible check of its stated mechanisms
and source identities, not a formal proof or a new analytic import.
