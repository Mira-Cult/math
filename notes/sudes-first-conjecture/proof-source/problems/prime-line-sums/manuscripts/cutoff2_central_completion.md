# Central diagonal preassignment and completion near the original mean

*Presentation copy: mathematical delimiters and equation labels are adapted for GitHub rendering. The unchanged, hash-bound source is in the [complete replay packet](../../../../packet/README.md).*


Author: `/root/prefix_balance_research`. The proposal to preassign both
diagonals from a narrow central stock is due to `/root/controller_redesign`.
This is a separate elementary completion component. It changes none of
FP, CY, RF, or any frozen controller. Independent nonauthor review of the
exact scientific revision is required. No numerical square cutoff or
formal-verification claim is made.

The prescribed pool is defined in [PROBLEM.md](../PROBLEM.md). The generic
lemma below applies to distinct real values, and hence to the unused
members of that pool. Its CY specialization uses only the finite support
facts in [CY5--CY6](cutoff2_cyclic_residue_centering.md), the factor lemma
[RF1](cutoff2_regular_factor_completion.md), and the rectangle support
[RP1](cutoff2_rectangle_packing.md). No analytic prime-count theorem is
imported here: the displayed central-stock counts are premises concerning
the **actually unused** values after all earlier reservations.

## CC1. Precise initial state and stock hypotheses

Let n>=20 be odd. An n-by-n partial array has distinct prescribed
values and N_0 still-empty cells, where


```math
N_0\ge3n^2/4.
 \qquad\text{(CC1)}
```


Its distinct unused value set S_0 has exactly N_0 elements, lies in an
interval of width less than X, and has mean mu. The center is empty.
After counting the center once, let q_1 and q_2 be the numbers of other
empty cells on the first and second main diagonal. Thus


```math
0\le q_i\le n-1,\qquad s=1+q_1+q_2\le2n-1.
 \qquad\text{(CC2)}
```


The off-diagonal empty cells form a bipartite graph of rows and columns.
Assume it has a spanning k-regular factor F, with integer k>0. Define


```math
t=N_0-s-kn\ge0.
 \qquad\text{(CC3)}
```


These t cells are the off-diagonal empty cells outside F. If a_L is a
row or column's original number of empty cells, suppose


```math
a_L-k\le u.
 \qquad\text{(CC4)}
```


This joint count includes that line's diagonal preassignments **and**
its cells outside the factor. It must not be replaced by an unnecessarily
separate sum of maximum counts when the support gives a sharper value.

Take epsilon>0, set eta=epsilon X, and let c be a reference satisfying


```math
|\mu-c|\le\kappa\eta,\qquad0\le\kappa\le1/4.
 \qquad\text{(CC5)}
```


Use the central interval and two disjoint outer subintervals


```math
I=[c-\eta,c+\eta],\quad
 I_-=(c-\eta,c-\eta/2],\quad
 I_+=(c+\eta/2,c+\eta].
 \qquad\text{(CC6)}
```


Assume the following exact lower counts in the initially unused pool:


```math
|S_0\cap I_-|\ge s,\qquad |S_0\cap I_+|\ge s,
 \qquad |S_0\cap I|\ge s+t.
 \qquad\text{(CC7)}
```


The weaker actual-count version CC7 is useful in the CY application.
A simpler sufficient version, when t<=3n+1, is at least 3n+2 unused
values in **each** outer interval: their disjoint union has at least
6n+4 values, exceeding s+t<=5n. No independence of prime supplies is
assumed. If counts start from raw prime intervals, every preceding
reservation that can meet them must first be subtracted or counted
exactly. A count in I does not on its own imply either outer count.

## CC2. A bounded exact-cardinality selection

Suppose a current unused pool has mean nu strictly between
c-eta/2 and c+eta/2. Let q>=1, and suppose at least q currently unused
values remain in each of I_- and I_+. Sort **all** current unused
values in I as v_1<...<v_M. The sum of the first q is below q nu,
and the sum of the last q is above q nu. Consecutive q-window sums
increase by


```math
v_{i+q}-v_i\le2\eta.
```


One of the two windows adjacent to the crossing therefore has sum
within eta of q nu. Select the nearer one, breaking ties by its
first index. This is an exact q-element subset of distinct values.
For q=0 select the empty subset and give it error zero.

Apply this selection successively to the center (q=1), the q_1 empty
noncentral positions of the first diagonal, and the q_2 positions of
the second. Assign each selected batch bijectively to its positions.
The latter two position sets are disjoint; the common center has
already been filled once.

Let N_j,mu_j be the unused count and mean after batch j, with
N_0,mu_0=mu the initial data. Write e_j for that batch's sum minus
its size times mu_(j-1). The selection guarantees |e_j|<=eta, and


```math
\mu_j=\mu_{j-1}-e_j/N_j.
 \qquad\text{(CC8)}
```


Here j=1 is the center; the three batch sizes are 1,q_1,q_2.
The hypotheses required for every selection persist. Indeed


```math
N_j\ge N_0-s\ge3n^2/4-2n+1\ge n^2/2,
 \qquad n\ge20.
```


By induction, before and after any of the three batches,


```math
|\mu_j-c|\le(\kappa+6/n^2)\eta
 \le(1/4+3/200)\eta\lt \eta/2.
 \qquad\text{(CC9)}
```


The base case is CC5. The update CC8 gives the next bound, so there
is no circular use of a selection whose mean has not been bracketed.
Before a batch of size q, at most s-q values have previously been
removed. Each outer interval therefore still has at least q values
by CC7. This charges even adversarial removal from one outer interval.

Let A_Delta be the deviation of **all** s selected diagonal-union
values from s times the original mean mu. Then


```math
A_\Delta=-N_3(\mu_3-\mu)
          =\sum_{j=1}^3 e_j N_3/N_j,
 \qquad |A_\Delta|\le3\eta.
 \qquad\text{(CC10)}
```


The signed deviation is small regardless of the number of newly filled
diagonal cells. It is not bounded by charging eta for each such cell.

## CC3. Both diagonal errors relative to the original expectation

For each required line, its original completion expectation means its
already prescribed sum plus its original number of empty cells times mu.
The prescribed entries never change.

Put e_0=e_1 for the center error, f_1=e_2 and f_2=e_3 for the two
diagonal-batch errors. Set A=N_0-1 and B=A-q_1. The first completed
diagonal's error from its original completion expectation is


```math
e_0(1-q_1/A)+f_1,
```


whose absolute value is at most 2eta. For the second diagonal it is


```math
e_0(1-q_2/A)-(q_2/B)f_1+f_2.
```


Since A,B>q_i and B=A-q_1, its absolute value is at most


```math
\left(2+\frac{q_1q_2}{AB}\right)\eta
 \le\frac{201}{100}\eta.
 \qquad\text{(CC11)}
```


For the last inequality, A,B>=7n^2/10 when n>=20, and
q_1q_2<=n^2; hence q_1q_2/(AB)<=100/(49n^2)<=1/196<1/100.
The formulas also cover either q_i=0, with its corresponding batch
error zero. Later filling occurs off both diagonals, so these two
bounds persist in the final array.

## CC4. Fill the exceptional cells, then the regular factor

All s preassigned values came from I. At least t unused values of I
remain by CC7. Choose any t of them, bijectively assign them to the
t off-factor cells, and write A_E for their total deviation from t mu.
Every selected central value differs from mu by at most
(1+kappa)eta. In particular


```math
|A_E|\le t(1+\kappa)\eta.
 \qquad\text{(CC12)}
```


Exactly kn unused values remain. Their mean mu_F satisfies


```math
k(\mu_F-\mu)=-(A_\Delta+A_E)/n.
 \qquad\text{(CC13)}
```


Decompose the k-regular factor into k perfect matchings, sort the kn
values, and split them into k consecutive blocks of n values. Assign
one block bijectively onto each matching. Every row and column gets
one value from each block. Its deviation from the sum of block means
is at most the sum of block ranges, which is less than X because the
blocks are consecutive disjoint portions of a list of width less than X.
The matching decomposition follows from Hall's condition: each left
subset S has k|S| incident edges and hence at least |S| neighbors;
remove one matching and repeat. Equivalently, the elementary integral
augmenting-path proof in RF1 constructs the matchings.

For a row or column L, let A_(Delta,L) and A_(E,L) be its selected
diagonal and exceptional deviations from the **original** mean mu.
If z_L is the factor-block discrepancy, then the final line error
from its original completion expectation is exactly


```math
A_{\Delta,L}+A_{E,L}
       -\frac{A_\Delta+A_E}{n}+z_L,
 \qquad |z_L|\lt X.
 \qquad\text{(CC14)}
```


There are a_L-k<=u central assignments on that line. Combining
CC10, CC12 and CC14 proves the general row/column bound


```math
\boxed{\quad X+
   \left[(u+t/n)(1+\kappa)+3/n\right]\varepsilon X.\quad}
 \qquad\text{(CC15)}
```


This direct identity avoids charging successive changes of unused mean
again. The actual signed A_Delta+A_E may be retained if a caller knows
it; the displayed bound needs only the stock premises. Every initial
unused value and empty cell is used once, every previously prescribed
entry remains fixed, and both main diagonals remain independent after
their assignments. The lemma does not assert that these baseline line
sums are already prime.

## CC5. Specialize to the unchanged CY support

Use CY's exact ordinary occupied count rho on every row and column,
and its J jointly placed rectangles. Their rows and columns are
distinct and avoid the center; each rectangle has exactly one diagonal
cell. Require CY's factor gate rho+4<=n/4 and the stated placement
hypotheses. The numerical value of a reserved entry plays no role in
these support facts.

The original unused count and unfilled diagonal-union count are


```math
N_0=n^2-\rho n-4J,\qquad s=2n-1-J.
 \qquad\text{(CC16)}
```


CY5's removal of two temporary center edges puts the residual support
in RF1's degree interval `[n-rho-4,n-rho-2]`. Therefore it contains
a factor of degree k=n-rho-5>0. The removed edges remain ordinary
off-factor completion cells; no cell or value is discarded. CY6 gives


```math
t=3n-3J+1\le3n+1.
 \qquad\text{(CC17)}
```


Initially each row and column has either rho or rho+2 prescribed
cells, according as it misses or meets a rectangle. Hence


```math
a_L-k=(n-\rho-e_L)-(n-\rho-5)=5-e_L\le5,
 \quad e_L\in\{0,2\}.
 \qquad\text{(CC18)}
```


This is why the local bound is 5, not the separate maxima 2+4.
A central row/column has one newly assigned diagonal cell and four
exceptional cells; an ordinary noncentral line has two and three;
a rectangle line has only three central assignments in total.

The sufficient central-stock invoices become


```math
|S_0\cap I_-|,|S_0\cap I_+|\ge2n-1-J,
 \qquad |S_0\cap I|\ge5n-4J.
 \qquad\text{(CC19)}
```


Under CC1 and CC5, CC15 with u=5 gives the sharper actual-count
completion allowance


```math
\boxed{\quad
 X+\left[(1+\kappa)(8-3J/n+1/n)+3/n\right]\varepsilon X.
 \quad}                                                   \qquad\text{(CC20)}
```


Dropping the favorable J term gives, pointwise for every n>=20,


```math
X+\left[8(1+\kappa)+(4+\kappa)/n\right]\varepsilon X
 \le X+\frac{817}{80}\varepsilon X
 \lt  X+\frac{41}{4}\varepsilon X.
 \qquad\text{(CC21)}
```


This also covers both diagonal bounds CC11, since its epsilon
coefficient exceeds 201/100. If c=mu, the sharper coefficient is
`8-3J/n+4/n`, or at most `8+4/n` after dropping J. There is no
differentiation across rounded controller parameters: the argument
uses the actual integer rho,J,k,s,t and pointwise `1/n<=1/20`.

For the gap-two controller, there are no residue entries and rho is
the actual main ordinary count. The same completion argument also
applies to a nonempty CY residue family if its actual support,
reservation count and central-stock premises meet the hypotheses;
no residue prime-count or modular-repair invoice is changed here.

## CC6. Exact controls and proof boundary

Run with Python 3.12 and the complete bound source set:

```
python3 -B problems/prime-line-sums/code/cutoff2_central_completion.py
```

The standard-library checker imports no producer program. It checks
the scalar implications with exact rational arithmetic, finite
sorted-window selections and mean updates, including zero-size
diagonal batches and reference offsets of both signs. Actual-prime
fixtures start with precisely the first n^2 odd primes. They construct
the CY residual support, verify its center trim and exact regular
factor, perform the new central preassignment and exceptional filling,
decompose the factor, and independently recompute every line error,
the original expectation, the unchanged prescribed cells, and the
complete input permutation. The fixtures are mechanism controls,
not assertions of prime line sums or whole-conjecture verification.

Negative controls reject absent outer stock, insufficient total stock,
wrong reference means, repeated values, wrong batch cardinalities,
omitted center/mean charges, invalid factor degrees and malformed or
physically substituted source files. A complete exact nonempty source
map is required; no private artifact, network access, prime table or
third-party package is needed for reproduction.

The universal selection, factor and completion arguments are ordinary
mathematics. The checker is not a formal proof kernel. In particular,
it does not establish a prime supply in CC7/CC19 or certify a caller's
approximate-reference error CC5. Those must be proved at every actual
scale and after every relevant prior deletion before this component
can enter a complete numerical theorem.
