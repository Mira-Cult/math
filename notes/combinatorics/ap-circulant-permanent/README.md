# A direct recurrence for arithmetic progression circulant permanents

We give an explicit, division-free algorithm for the permanent of

```math
C_{ij}=A+B((j-i)\bmod n),\qquad 0\leq i,j<n.
```

It uses $`O(n^5)`$ arithmetic operations and $`O(n^4)`$ stored ring elements.
The proof applies to the larger family
$`M_{ij}=u_i+v_j+t\mathbf{1}_{j<i}`$. Four counters suffice: open staircase
columns, completed staircase edges, row-type rows, and row-type columns.
The other matchings are counted at the end by two factorials.

**Status and attribution.** This is a conventional mathematical proof with
executable exact-arithmetic checks and a scoped independent automated review,
not a formalization or an externally refereed paper. We make no priority,
optimality, or new-complexity-class claim. Flarup and Lyaudet's general
bounded-weighted-width perfect-matching theory already implies polynomial
tractability after a reduction. Their paper does not state this AP-circulant
corollary or the direct recurrence below. The explicit reduction and
specialization in [PRIOR_ART.md](PRIOR_ART.md) also give the same
$`O(n^5)`$ time and $`O(n^4)`$ space bounds. The purpose of this note is to state
the circulant result, prove the shorter direct recurrence, and make the bound
and its qualifications easy to check.

- [Implementation](permanent.py) and [exact tests](verify.py).
- [Relation to the weighted matching framework](PRIOR_ART.md).
- [Verification and review scope](VERIFICATION.md).

## 1. The general theorem and the circulant corollary

Let $`R`$ be a commutative ring with identity. For an $`n\times n`$ matrix,
write

```math
\mathrm{per}(M)=\sum_{\sigma\in S_n}\prod_{i=0}^{n-1}M_{i,\sigma(i)},
\qquad \mathrm{per}(\varnothing)=1.
```

**Theorem.** Given $`u_0,\ldots,u_{n-1},v_0,\ldots,v_{n-1},t\in R`$, the
permanent of

```math
M_{ij}=u_i+v_j+t\mathbf{1}_{j<i}
```

can be computed with $`O(n^5)`$ ring operations and $`O(n^4)`$ ring elements of
working storage. The algorithm uses addition and multiplication only. No
positivity, division, nonzero-parameter, or characteristic-zero hypothesis
is needed.

**Corollary.** The same bounds hold for arithmetic progression circulants.
For $`n\geq1`$,

```math
(j-i)\bmod n=j-i+n\mathbf{1}_{j<i},
```

so substitute

```math
u_i=A-iB,\qquad v_j=jB,\qquad t=nB.
```

The empty case is defined separately. The opposite circulant convention
transposes the matrix and therefore has the same permanent. The theorem is
not an algorithm for arbitrary circulant first rows, arbitrary independently
weighted lower triangles, or arbitrary dense matrices. The general family
contains matrices outside the AP-circulant family. For example, over the
integers at $`n=2,t=0,v=0,u=(0,1)`$, it includes the matrix with rows
$`(0,0)`$ and $`(1,1)`$, which is not a circulant.

## 2. The direct four-counter recurrence

All counters below are nonnegative integers. Unspecified table entries are
zero. Let $`D_i(h,k,r,c)`$ be the table after processing rows and columns
$`0,\ldots,i-1`$. Initialize

```math
D_0(0,0,0,0)=1.
```

For $`i=0,\ldots,n-1`$, first start an empty row table $`E_i`$. For each
state of weight $`w=D_i(h,k,r,c)`$, perform the following additive updates:

```math
\begin{aligned}
E_i(h-1,k+1,r,c)&\mathrel{+}=htw &&(h>0),\\
E_i(h,k,r+1,c)&\mathrel{+}=u_iw,\\
E_i(h,k,r,c)&\mathrel{+}=w.
\end{aligned}
```

Then start an empty next table $`D_{i+1}`$. For each state of weight
$`w=E_i(h,k,r,c)`$, perform

```math
\begin{aligned}
D_{i+1}(h+1,k,r,c)&\mathrel{+}=w,\\
D_{i+1}(h,k,r,c+1)&\mathrel{+}=w,\\
D_{i+1}(h,k,r,c)&\mathrel{+}=v_iw.
\end{aligned}
```

Here $`\mathrel{+}=`$ means "add to the existing entry," not "replace it."
In particular, the row is processed **before** the column with the same
index. The answer is

```math
\boxed{\mathrm{per}(M)=
\sum_{\substack{k,r\geq0\\k+r\leq n}}
D_n(0,k,r,r)\,r!\,(n-k-r)!.}
```

The factorials and integer multipliers are interpreted in $`R`$ via its
canonical map from the integers. Thus this formula also works in positive
characteristic, even when a factorial vanishes.

**Optional pruning.** After a column step, with $`m=n-i-1`$ indices left,
discard any new state with $`h>m`$ or $`|r-c|>m`$. The implementation uses both
tests. Neither is necessary for correctness or the asymptotic bound.

## 3. Proof by colored endpoints

Expand every selected matrix entry in each permutation monomial into one of
three types:

- $`U`$: use its row contribution $`u_i`$;
- $`V`$: use its column contribution $`v_j`$;
- $`T`$: use $`t`$, allowed only when $`j<i`$.

The $`T`$ entries form a partial matching in the strict lower triangle.
Every remaining row and column is assigned type $`U`$ or $`V`$. For these
types we postpone choosing the actual bijections until all endpoints have
been assigned.

### The prefix invariant

After processing the first $`i`$ row-column pairs,
$`D_i(h,k,r,c)`$ sums the weights of partial objects having:

1. $`k`$ processed $`T`$ rows, each matched to a distinct earlier $`T`$ column;
2. $`h`$ additional processed $`T`$ columns still waiting for later rows;
3. $`r`$ processed $`U`$ rows and $`c`$ processed $`U`$ columns;
4. type $`V`$ on every other processed endpoint.

The weight of such an object is

```math
t^k\prod_{a\text{ a }U\text{ row}}u_a
    \prod_{b\text{ a }V\text{ column}}v_b.
```

Different partial $`T`$ matchings are counted separately. No $`U`$ or $`V`$
edges have yet been selected. The empty object proves the initial condition.

### The row and column steps preserve the invariant

A new $`T`$ row can choose any of the $`h`$ open columns. All have smaller
indices, all give weight $`t`$, and removing any one leaves the same future
possibilities as far as the counters are concerned. This gives multiplier
$`ht`$, decreases $`h`$, and increases $`k`$. A new $`U`$ row contributes
$`u_i`$ and increases $`r`$. A new $`V`$ row contributes no factor yet. These
are exactly the three row updates.

A new $`T`$ column is reserved for a later row and increases $`h`$. A new
$`U`$ column increases $`c`$. A new $`V`$ column contributes $`v_i`$. These
are the three column updates. Because column $`i`$ is not open when row
$`i`$ is processed, a diagonal $`T`$ edge can never be introduced.

The identities of open columns need not be retained: every future row can
use every open column with the same weight, and those columns will never
participate in a $`U`$ or $`V`$ edge. For a fixed partial object each new
endpoint has exactly one of the listed types. Counting its possible $`T`$
partners by $`h`$ neither loses nor duplicates any object.

### The terminal factorials complete the permanent

A complete object must have $`h=0`$. It has $`n-k`$ endpoints on each side
left for $`U`$ and $`V`$ edges. Their type counts agree exactly when $`r=c`$.
There are then $`r!`$ bijections between the $`U`$ rows and columns, and
$`(n-k-r)!`$ bijections between the $`V`$ rows and columns. Every bijection
within one type has the same weight, already recorded in the state.

Each fully expanded permutation monomial uniquely specifies its $`T`$
matching, its endpoint types, and its two remaining bijections. Conversely,
these data specify such a monomial. Summing the terminal weights with the
two factorials proves the formula. The proof is a polynomial identity over
the integers and therefore remains valid over every commutative ring.

For pruning, each open column needs a different later row, so $`h>m`$ cannot
be completed. Each remaining row-column pair changes $`r-c`$ by at most one,
so $`|r-c|>m`$ cannot be completed either. These are only necessary conditions;
leaving other dead states in the table causes no problem.

## 4. Complexity and exact computation

### Ring operations and storage

Every counter lies between $`0`$ and $`n`$. Each of the $`2n`$ layers has at
most $`(n+1)^4`$ entries and three constant-cost transitions per entry.
Rolling tables therefore use $`O(n^5)`$ ring operations and $`O(n^4)`$ ring
elements. Precompute the integer scalars and factorials in $`O(n)`$ ring
operations. The final sum has $`O(n^2)`$ terms.

Dense four-index arrays realize deterministic indexed access to the states.
The supplied Python implementation uses dictionaries for convenience and
usually avoids many unreachable states. The arithmetic-operation theorem
does not make Python hashing, large integers, or symbolic expressions
unit-cost machine operations.

### Integers and rationals

Suppose the absolute values of $`u_i,v_j,t`$ are less than $`2^L`$, with
$`L\geq1`$, and set $`D=L+\lceil\log_2(n+1)\rceil+O(1)`$. There are at most
$`9^n`$ endpoint-type histories, at most $`n^n`$ choices of staircase
partners, and at most $`2n`$ input factors per history. Hence all state
values and terminal intermediate values have $`O(nD)`$ bits, even with
signed inputs and cancellation. Each transition multiplies by an input
or a counter with $`O(D)`$ bits. Schoolbook arithmetic gives the safe bounds

```math
O(n^6D^2)\text{ bit operations},\qquad
O(n^5D)\text{ bits of working storage}.
```

For AP parameters $`|A|,|B|<2^L`$, the transformed inputs acquire only
$`O(\log(n+1))`$ extra bits, so the same displayed bounds hold with this
definition of $`D`$, up to constants.

For rational inputs, let $`d`$ be a positive common denominator and compute
the integer instance $`(du,dv,dt)`$, then divide the answer by $`d^n`$.
If each of the $`2n+1`$ rational inputs has numerator and denominator of at
most $`L`$ bits, $`d`$ and the scaled inputs have $`O(nL)`$ bits. Substituting
$`D=O(nL+\log(n+1))`$ gives a polynomial bit bound; final rational reduction
is polynomial too. In the AP case there are only two input denominators,
so $`d`$ and the scaled $`A,B`$ have $`O(L)`$ bits instead. Exact `Fraction`
arithmetic is supported by the implementation.

### Symbolic output and input encoding

The ring-operation count applies to evaluation in a specified coefficient
ring. It is not a promise of polynomial-size expanded output in all the
independent variables $`u_i,v_j,t`$.

For the AP specialization, every term of a state after $`i`$ pairs has the
same total degree in $`A,B`$:

```math
k+r+(i-k-h-c)=i+r-h-c\leq2n.
```

Thus a state needs only $`O(n)`$ homogeneous bivariate coefficients.
Multiplication by $`A-iB`$, $`iB`$, or $`nB`$ takes a linear pass through
them. A dense coefficient implementation gives $`O(n^6)`$ integer-coefficient
operations and $`O(n^5)`$ coefficients of storage. Coefficient bit lengths
are $`O(n\log(n+1))`$; a conservative schoolbook bound is
$`O(n^7\log^2(n+1))`$ bit operations. The scalar implementation does not
claim that a generic symbolic-expression package automatically realizes
these coefficient bounds.

All complexity statements are polynomial in the dimension $`n`$ and the
input coefficient size, not in $`\log n`$ for a succinct binary dimension.
For example, $`A=1,B=0`$ gives $`n!`$, which already has
$`\Theta(n\log n)`$ output bits. Floating-point evaluation is not guaranteed
to be stable; the decomposition can involve substantial cancellation.

## 5. Examples and reproduction

For $`n=2`$ the first row is $`(A,A+B)`$ and

```math
\mathrm{per}(C)=A^2+(A+B)^2.
```

For $`n=3`$ it is $`(A,A+B,A+2B)`$ and

```math
\mathrm{per}(C)=A^3+(A+B)^3+(A+2B)^3+3A(A+B)(A+2B).
```

In particular, $`\mathrm{per}(\mathrm{Circ}(1,2,3))=54`$.
The first values at $`A=0,B=1`$, for $`n=1,\ldots,8`$, are

```text
0, 1, 9, 164, 5050, 227508, 14064519, 1146668608.
```

These agree with [OEIS A086759](https://oeis.org/A086759), whose addition-table
convention differs by a row permutation. If $`B=0`$, the formula reduces to
$`n!A^n`$, including $`n=0`$ by the empty-product convention.

From this directory, with Python 3.10 or later and no third-party packages:

```sh
python permanent.py 3 1 1
python permanent.py -- 5 1/2 -2/3
python verify.py
python check_gadget.py
python check_profile.py
```

The first command prints `54`. The `--` allows negative fractions as
positional arguments. `verify.py` compares the implementation
against independent subset and permutation algorithms, checks signed and
rational inputs, finite rings, polynomial identities, and constant matrices.
The two additional scripts check the prior-art reduction and its specialized
matching recurrence. Tests supplement the proof; their finite ranges are
listed in [VERIFICATION.md](VERIFICATION.md).
