**Public reading copy.** Presentation and links have been normalized. Historical status statements below belong to their source revisions; see the [current publication status](../../README.md#review-and-verification-status). The matching original bytes are in the [source archive](../../originals/manuscripts/hyperk_resources.md).

# Uniform resource estimates for a finite fixed-dimension controller

Author: `/root`. These are conventional analytic, arithmetic and probabilistic
lemmas. They do not assert the missing bounded-load controller for every full
signed line. The distinction between a numerical ledger and a physical packing
proof is part of their hypotheses. All labels are manuscript-local.

## 1. Quantifiers and the finite-depth ladder

Fix an integer k >= 2. Then fix a finite depth D >= 0, a maximum number M >= 1
of prime pairs per simultaneous stage, a finite bound C on the geometric
constants, and a finite logarithmic exponent b >= 0. These quantities may
depend on k. They must not depend on the subsequently increasing odd n.
Write


```math
P_n=\{p_2,\ldots,p_{n^k+1}\},\quad X=\max P_n,\quad
 T=\sum_{p\in P_n}p,\quad \bar p=T/n^k,\quad \mu=n\bar p.
```


The prime number theorem and partial summation give


```math
X\sim k n^k\log n,\qquad \bar p\sim X/2,\qquad
 \mu\sim (k/2)n^{k+1}\log n.                         \qquad\text{(R1)}
```


Choose


```math
a_j={3\over5}+{3j\over20(D+1)},\qquad
 K_j=\lceil n^{a_j}\rceil\quad(0\le j\le D),\qquad
 \delta=n^{-1/5}.                                    \qquad\text{(R2)}
```


In particular


```math
a_D={3\over4}-{3\over20(D+1)}\lt {3\over4},\qquad
 a_{j+1}-a_j={3\over20(D+1)}\gt 0.                       \qquad\text{(R3)}
```


This is a formula for every finite D, not a list of numerical exponents
extrapolated indefinitely. Its adjacent gaps shrink with D, while its endpoint
always stays strictly below 3/4. No assertion for growing k or D is made.

**Lemma RL (resource ladder).** For the quantifiers above, with any even
g <= 16 ceil(log_2 X), every fixed power of log n is absorbed in each strict
comparison below:


```math
\begin{split}
 &\sqrt{n\log n}=o(K_0),\quad K_D=o(n),\quad
 \delta K_D=o(K_0),\quad \sqrt{K_D\log n}=o(K_0),\\
 &K_j(\log n)^b=o(K_{j+1})\quad(j\lt D),\\
 &n^{k-1}K_D(\log n)^b=o\!\left({\delta X\over g\log X}\right),\\
 &g n^{k-1}(\log n)^b=o(K_jX),\qquad
 \mu^{3/5}=o(X),\\
 &n^{k-1}(\log X)^b=o\!\left({X\over(\log X)^{b+2}}\right).
                                                               \qquad\text{(R4)}
\end{split}
```


For the last line the two occurrences of b may be replaced by any two fixed
exponents. Proof: compare powers of n using (R1). The minimum gap for the
worst deletion inequality is


```math
(k-1/5)-(k-1+a_D)=4/5-a_D\gt 1/20.
```


The midpoint gap is also 4/5-a_D > 1/20; the square-root completion gap is
3/5-1/2=1/10; the whole-bundle fluctuation gap is 3/5-a_D/2 > 9/40.
The rounding gap is 1+a_j >= 8/5. Finally,


```math
{\mu^{3/5}\over X}\asymp_k
 n^{(3-2k)/5}(\log n)^{-2/5}\longrightarrow0
```


for every k >= 2. The adjacent gap in (R3) is positive at every fixed D.
Ceilings only contribute bounded factors. This proves the lemma. QED.

## 2. Analytic input and simultaneous fresh matching

We use the printed short-interval progression consequence of Thorner and
Zaman, *Refinements to the prime number theorem for arithmetic progressions*,
arXiv:2108.10878v2, Section 1.2, following equation (1.6). For each fixed
epsilon > 0 and A > 0 it gives a uniform weighted prime asymptotic in reduced
classes modulo q <= (log x)^A when the interval length is at least
x^(7/12+epsilon) (log x)^A. The ineffective Siegel step in Remark 1.2 is
retained. This is the same input used in the frozen
[four-dimensional supply proof](hyper4_axis.md), Section 2, and
[cube targets](cube_targets.md). The argument here checks the arbitrary-k
substitution and arbitrary finite tuple size rather than treating 40 as universal.

Put F=ceil(100 log X), B_M=256(M+1), and


```math
P_M=\lceil B_M F^2\rceil+32F\lceil\log_2 X\rceil.    \qquad\text{(R5)}
```


The letter P_M denotes a stage count, not the prime pool. It is O_k(log^2 X)
when M=M(k) is fixed. Suppose the planned collection has at most
C n^(k-1) main reservoirs, at most P_M uncontrolled prefix stages and 33K_D
macro stages per reservoir, at most C n^(k-1)g residue stages, and at most
M disjoint prime pairs per stage. Enlarging C to include 2M and finite pass
counts gives the full endpoint invoice


```math
Q\le C n^{k-1}(P_M+K_D+g).                           \qquad\text{(R6)}
```


**Lemma FS (fresh supply).** Every such collection can be assigned distinct
prime endpoints from the exact pool, with the following properties, after
all of its cell slots have been legally planned. All requested prefix seed
stages have one common even difference g <= 16 ceil(log_2 X). Each subsequent
growth or macro stage has its own positive difference divisible by g and at
least its requested number, at most M, of disjoint pairs. A macro difference
lies in [X/4,X/2] and every pair midpoint is within delta X of the exact mean
bar p. A residue stage instead has a common difference congruent to 2 modulo g.
All previous endpoints may be concentrated in the worst requested interval
and reduced residue class. No endpoints are reused, and unselected entries
remain available for completion.

### 2.1 A single seed matching

There are asymptotically X/(2 log X) primes in [X/4,3X/4]. Pair consecutive
members disjointly; the sum of the pair gaps is at most X/2. Thus a positive
proportion of these disjoint pairs have gap at most 8 log X, and eventually
at most 16 ceil(log_2 X). Every gap is even. Pigeonholing the O(log X) possible
gaps gives >> X/log^2 X disjoint pairs with one actual gap g. Their endpoints
exceed g eventually, so the lower endpoint is in a reduced class modulo g.
Pigeonhole the at most g classes once more to obtain >> X/log^3 X pairs in
one common reduced lower class r. The constants are independent of the
selected g and r.

Reserve every seed endpoint before allocating any other prime. The seed demand
is O_k(n^(k-1)P_M)=O_k(n^(k-1)log^2 X), which is o(X/log^3 X) by RL.
This is an actual disjoint matching, not a conjecture about infinitely many
bounded prime gaps. The selected gap is allowed to vary with n.

### 2.2 Uniform counts after arbitrary deletion

Use the two intervals


```math
I_\pm=[\bar p\pm X/6-\delta X,\;\bar p\pm X/6+\delta X].
                                                               \qquad\text{(R7)}
```


They eventually lie in [X/4,3X/4]. Their relative interval exponent satisfies


```math
{\log(\delta X)\over\log X}\longrightarrow1-{1\over5k}
 \ge9/10\gt 7/12.
```


Fix an intervening exponent and a positive epsilon smaller than its gap above
7/12. The printed analytic input with A=3 therefore applies uniformly to
every reduced class modulo every allowed g. Each class has
>> delta X/(g log X) primes in each I_+ and I_-, and >> X/(g log X) in a fixed
positive-length proportion of [X/4,3X/4]. By RL,


```math
Q=o(\delta X/(g\log X)),                              \qquad\text{(R8)}
```


uniformly over allowed g. Consequently deleting all endpoints allowed by
(R6) leaves at least half the indicated supply eventually, even if every
deletion lies in the currently requested interval and class. This includes
seed deletions, all earlier stages and all other controller families.

### 2.3 Grouped growing differences, for any finite M

Suppose a fresh set S in a single class modulo g lies in an interval of length
at most X, has at least X/(gF) members, and


```math
B_M g F^2\le R\le X.
```


Partition into at most 2X/R bins of length at most R. Some bin contains
s >= R/(2gF) members. Because distinct members are at least g apart, fewer
than s^2/16 unordered pairs have distance below gs/16. Since s is sufficiently
large under the displayed bound, at least s^2/4 pairs have distance at least
gs/16. Pigeonholing at most R/g positive differences produces one difference


```math
{R\over32F}\le d\le R,\qquad d\equiv0\pmod g,
```


with at least R/(16gF^2) >= 16(M+1) edges. The fixed-difference graph has
maximum degree two, so a greedy matching has at least one third as many
edges; in particular M mutually disjoint pairs exist. The density from
Section 2.2 is larger than X/(gF) after deletion, so this may be applied afresh
at every growth request.

Give each scalar reservoir ceil(B_M F^2) seed stages. Its subset sums contain
the complete g-grid from 0 to R >= B_M gF^2. When R<X, append a growth stage.
Its gap is at most R, so the two translates of the old grid interval overlap
or touch on the grid; their union is the grid to R+d. Growth is by a factor
at least 1+1/(32F). The bound
log(1+1/(32F)) >= log(2)/(32F) gives at most 32F ceil(log_2 X) additional
stages before R>=X. The final endpoint is at most 2X. This proves the complete
prefix bound P_M, including multiplicities of actual physical pairs.

### 2.4 Macro and residue differences

After the full deletion allowance, choose fresh primes from I_- and I_+
in the same reduced class r. Each set has >> delta X/(g log X) members.
There are at most X/g+1 possible differences. Some difference has


```math
\gg {\delta^2 X\over g\log^2X}                      \qquad\text{(R9)}
```


representations. For a fixed difference the low/high pairs are already
disjoint: each lower and each upper endpoint has a unique partner. The two
intervals themselves are disjoint. The bound (R9) tends uniformly to infinity,
since its power of n is at least k-2/5. Hence M fresh pairs are available.
Their midpoint lies within delta X of bar p; their difference is in [X/4,X/2]
for all sufficiently large n. Use exactly the requested number of pairs and
charge every selected endpoint immediately to (R6).

For residue stages use lower class -1 and upper class +1 modulo g. These are
always reduced classes, including g=2. The same argument gives M pairs whose
common difference is 2 modulo g. Small primes dividing g need not be put in
any stage; they remain in the unused pool. This completes FS. QED.

## 3. Complete scalar intervals and both legal reference states

Append ceil(32K_j) macro stages to a reservoir at level j. The complete prefix
already reaches X, and all macro differences are at most X/2, so its subset
sums remain a complete g-grid. If R_b is the total gap of all stages, then


```math
8K_jX\le R_b=O_k(K_jX).
```


Choose a subset of total q_b=g floor(R_b/(2g)), and also its complement.
These are legal configurations on the same actual entries and disjoint cells.
Their scalar totals differ by at most g. From either state, every multiple
of g with signed magnitude at most 3K_jX is attainable eventually. This is
an interval assertion, stronger than a gcd or residue assertion.

All pairs of one simultaneous stage switch together. A scalar reservoir may
use a bounded compound geometry only if that geometry's two orientations and
its complete signed-line signature have separately been proved. An abstract
integer coefficient does not license overlapping cells. If a finite larger
capacity factor is needed, multiply 32 by that factor; every estimate above
allows this fixed-in-k change.

## 4. Joint centering of complete bundles and the exact unused pool

**Lemma JC (joint centering).** In addition to the proved fresh-value supply,
assume the geometry has been planned pairwise disjointly and has these three
properties for every full signed line, including lines not in the eventual
target family:

1. At most C(P_M+g) cells lie in prefix or residue stages, and at most C K_D
   in macro stages.
2. For every main reservoir, its two complementary central reference states
   have line-sum difference at most C X on every full signed line.
3. Every macro cell is one endpoint of one of the pairs in FS, and is switched
   to its partner when the reservoir reference state is complemented.

Then the exact prime pool has a baseline permutation with all full signed
line sums mu+o(K_0X), while retaining every reserved reservoir's two-sided
capacity. No independent-cell randomization or arbitrary partial prime array
is part of the conclusion.

Proof. Fix residue stages. Independently choose one of the two complementary
reference states of each complete main reservoir, with probability 1/2.
Every macro cell has its pair midpoint as expectation. If r_L is the number
of reserved cells on a line L and C_L their sum, then


```math
|\mathbb E C_L-r_L\bar p|
 \le C\{\delta K_DX+(P_M+g)X\}.                     \qquad\text{(R10)}
```


At most r_L reservoirs meet L, since distinct reservoirs have disjoint cells.
Hoeffding's independent bounded-variable estimate applied to their *whole*
contributions, followed by a union bound over
L_k(n)=((n+2)^k-n^k)/2=O_k(n^(k-1)), gives one simultaneous reference choice
with


```math
|C_L-r_L\bar p|\le E,
 \quad E=O_k\!\left(\delta K_DX+(P_M+g)X+
           X\sqrt{(K_D+P_M+g)\log n}\right).          \qquad\text{(R11)}
```


The constant in the deviation is chosen after k and C. This argument allows
arbitrary dependence among all cells of a reservoir. In particular it does
not falsely treat the pairs of a simultaneous checkerboard as independent.

Let U be the number of unused entries. By (R6), U>=n^k/2 eventually. Summing
(R11) over one full axis partition counts every reserved cell exactly once,
so the actual unused mean obeys


```math
|\bar p_{\rm unused}-\bar p|
 \le {n^{k-1}E\over U}\le {2E\over n}.                \qquad\text{(R12)}
```


Fill the unoccupied cells by a uniform bijection of every remaining prime.
The expected completed line sum differs from mu by at most 3E. Sampling
without replacement from [0,X] satisfies the bounded-range estimate


```math
\Pr(|S_L-\mathbb E S_L|\gt u)
 \le2\exp(-u^2/(2nX^2)).                             \qquad\text{(R13)}
```


For completeness, expose the at most n selected unused entries in the line.
The martingale difference for the final sum on revealing the next sampled
entry is (1-(s-i)/(U-i)) times its deviation from the remaining mean, where
s is the number of unoccupied cells and i the number exposed. Its absolute
value is at most X. The elementary bounded-difference martingale inequality
gives (R13). It also covers s=0 with zero deviation.

Taking u=2X sqrt((k+2)n log n) and summing probabilities over L_k(n) gives
a quantity tending to zero. Some completed bijection has all full signed
line sums within 3E+u of mu. By RL, E+u=o(K_0X). Every originally prescribed
prime occurs exactly once: the reserved assignment was injective and the
remaining assignment is a bijection of its complement. This proves JC. QED.

## 5. Complete symbolic ledger and its logical boundary

The common estimates are collected here so their dependence on geometric
hypotheses is visible. Fixed constants may depend on k,D,M,C,b only.

| Resource or obligation | Paid bound | Strict comparison or geometric source |
|---|---|---|
| Full line inventory | ((n+2)^k-n^k)/2 | Exact geometry; O_k(n^(k-1)) for union bounds |
| Main reservoirs | <= C n^(k-1) | Must be proved by the actual controller |
| Equal-gap pairs per stage | <= M(k) | Must be proved for each simultaneous template |
| Prefix per reservoir | P_M=O_k(log^2 X) | Complete grid, Section 2.3 |
| Global seed invoice | O_k(n^(k-1)log^2 X) | o(X/log^3 X) |
| All reserved entries | O_k(n^(k-1)(P_M+g+K_D)) | o(n^k) and full worst-deletion bound R8 |
| Fresh narrow-class supply | >> delta X/(g log X) | Larger by a power >1/20 than total reserve |
| Repeated macro differences | >> delta^2X/(g log^2 X) | Tends uniformly to infinity, exceeds M(k) |
| Per-line prefix/residue cells | O_k(P_M+g) | Separate family/stratum packing proof required |
| Per-line macro cells | O_k(K_D)=o(n) | Separate family/stratum packing proof required |
| Per-reservoir contribution range | O_k(X) | Complete-bundle signature/freshness proof required |
| Midpoint bias | O_k(delta K_DX) | o(K_0X), slack >1/20 |
| Random bundle fluctuation | O_k(X sqrt((K_D+P_M+g)log n)) | o(K_0X), slack >9/40 |
| Unused-pool mean | <=2E/n per entry | Derived from exact directional partition, R12 |
| Random unused completion | O_k(X sqrt(n log n)) per line | o(K_0X), slack 1/10 |
| Prime-target window | mu^(3/5) | o(X) for every k>=2 |
| Later flow coefficient | O_k(K_jX log^b n)+O_k(g n^(k-1)) | o(K_(j+1)X) |
| Residues modulo g | actual steps 2 mod g, coefficient modulo g/2 | No division by a nonunit; geometric solver still required |

The table closes every displayed analytic inequality for any *proved finite*
controller depth and the stated polynomial support counts. It does not prove
those support counts. In particular, the fixed-marker kernel basis in the
[integer manuscript](hyperk_incidence.md) cannot be substituted for the
per-line packing hypotheses: even a bounded-support basis vector can occur
in an unbounded number of basis supports at the same cell.

The [axis and majority-line controller](hyperk_controller.md) verifies its
own geometric hypotheses. The sought all-full-line controller must still
verify its named signed-kernel generation and packing interface. If that is
proved with a finite depth D(k), this same ledger gives one eventual odd tail
by taking the maximum of finitely many thresholds. The analytic threshold is
possibly ineffective. Neither 3^k in IK nor any finite diagnostic order is
asserted to be a sufficient prime-array threshold.

## 6. Reproduction and failed scale choices

Run `python3 -B problems/prime-arrays-beyond-square/code/hyperk_resources.py`.
It checks exact rational exponents, including k=5 and k=6 and arbitrary supplied
finite depth; it also rejects endpoint exponents 4/5 and above because the
worst-deletion and midpoint margins then disappear or reverse. Its symbolic
coefficient checks verify the identities behind RL, not analytic distribution
at any finite n. A finite successful ledger is not a proof for growing k.

The older four-dimensional decimal sequence cannot simply be continued with
a fixed increment forever. Formula (R2) replaces that failed shortcut. The
other failed shortcut is global occupancy alone: R6 never implies the per-line
or section hypotheses of JC. These are independent, necessary packing tasks.

## References and source boundary

- Thorner--Zaman, arXiv:2108.10878v2, Theorem 1.1, Remark 1.2, equation (1.6)
  and Section 1.2: uniform short-interval AP counts, with ineffectivity retained.
- Mira-Cult/math-wip `a2445962ec6e06b2a893980fb7a183057eb9bcee`,
  `cube_controller.md`, Sections 2--3: inherited elementary pair and graph
  mechanisms; the present argument restates the needed arbitrary-M supply.
- Mira-Cult/math-wip `b837e307fc41975d0fb332c8215d6835ba47a271`,
  `hyper4_axis.md`, Section 2, and `hyper4_cube.md`, Sections 2--3: frozen
  four-dimensional comparisons and complete-bundle centering. No new cutoff
  campaign source or numerical bound is imported.
