# Independent review: joint targets and uniform resources

Reviewer: `/root/targets_resources_review`. Review date: 2 November 2026.

Exact frozen scientific revision:
`5692d37633ef4b509e8429cddf4ed762e7235d08` (PR83).

**Verdict: no blocking defect found in the reviewed target and resource
arguments.** This covers KP, the weight and gcd calculation, KW and KPT in
[hyperk_targets.md](../manuscripts/hyperk_targets.md), and RL, FS, the complete
scalar intervals, and JC in
[hyperk_resources.md](../manuscripts/hyperk_resources.md). The resource result
retains its explicitly stated geometric hypotheses. It does not establish
them for any controller by itself.

## Authorship, scope and source binding

I was assigned this review after the scientific commit was frozen. I did not
author any reviewed manuscript, target producer, resource ledger, target
fixture, controller, or imported source. My additions are this review and
[hyperk_targets_resources_controls.py](hyperk_targets_resources_controls.py).
I did not change author files, claims, inputs or Git references.

This is conventional internal mathematical review, not a formal GitHub
approval, remote CI run, or proof-kernel verification. I reviewed the prime
target interface and the analytic, arithmetic and probabilistic resource
arguments. I have not reviewed the full integer-incidence theorem, the physical
axis or majority controller's geometry, the newer half-coordinate proposal,
or a distributed full signed-kernel controller. Their assertions must not
inherit acceptance from this review.

I read the working agreement, research protocol, required problem records,
the complete two frozen manuscripts and their code. All replays used a
separate `git archive` of the exact scientific commit. The following source
bytes and the two retained higher-dimensional target inputs were compared
with `git show` at that commit. The reviewer program enforces seven SHA256
bindings before importing the author arithmetic routines.

| Source | SHA256 |
|---|---|
| `manuscripts/hyperk_targets.md` | `2a69a31ce1a3ecde164bf7748dc52c22b2637551bc97dd821edd497ea9df5306` |
| `manuscripts/hyperk_resources.md` | `c26bd5d67dd3dee746c986c1d11695a4ba92d2aeda53f0e5441b1adf113ce0a7` |
| `manuscripts/cube_targets.md` | `b92be738cd42c0ec61c6ed40004c267ce631ba08dc37899656cd1055f8388559` |
| `code/hyperk_targets.py` | `6fa292732db53e6ce17a388fdd34dfd5cc476e858887fb6c3df2a699335cfb9f` |
| `code/hyperk_resources.py` | `4c17e6cbbd1e3a2cd0a1f89057ccf283870222deea82ab3ee0554b3804bac2e7` |

I separately fetched the exact imported
[FL source at `c2118dfad1aeb660d66308dc6a94d6c959f5010c`](https://github.com/Mira-Cult/math-wip/blob/c2118dfad1aeb660d66308dc6a94d6c959f5010c/problems/prime-line-sums/manuscripts/explicit_prime_targets.md)
through the GitHub connector. The returned blob was
`e9ee67afb4ba70aba454576ed88834b42d11fcf5`; the bytes have SHA256
`0e6ff5f0c26c6a2a6e66d0ae2b1a2ef581f282662a8e772e827ba04fd72f45e1`,
matching the manuscript's pin. That older commit is not available as a local
tree in this clone; I do not represent the remote fetch as a local Git-object
replay. I read its complete finite-list proof and checked the interface used
here. I also reopened the primary
[Thorner--Zaman paper, arXiv:2108.10878v2](https://arxiv.org/pdf/2108.10878v2),
especially the printed short-interval consequence on page 3 and its stated
ineffectivity. No more recent cutoff campaign or unpinned analytic substitute
was used.

## Target construction

### All signed partitions and exact combinatorial weights

The target prescription depends on the ordinary set of absolute fixed labels.
For a two-parameter section with disjoint nonempty varying blocks, both
partition sums have term `q_(S union {|t|})` at the same parameter `t`.
Coordinate signs, repeated fixed labels, and the central label do not change
that identity. This proves every stated two-block identity, including
complementary traces, without first assuming saturation. A body-line target
never appears in such an identity, so using the center prime for the empty
fixed-label set imposes no hidden equation.

The no-zero weights count onto maps to a prescribed set of `s` labels, with
two signs for each occurrence. The zero-containing weights first require an
occurrence of zero and then use inclusion-exclusion to require all nonzero
labels. The unique all-zero tuple gives weight one. These cases partition
the full axis tensor, proving K4. At most `2r` signed representatives are
available to a set of at most `r` labels, so `(2r)^r` is a valid common
weight bound. The two finishing classes each have exactly `m` variables;
the zero-containing class is present for `r>=2` and correctly absent for
`r=1`.

The gcd proof is integral. One finishing weight is `2^r`, so the gcd has
no odd prime factor. For odd `r>=3`, the other is `2 mod 4`. For even
`r=2^u v`, repeated squaring and an odd geometric sum give
`nu_2(3^r-1)=u+2`. Taking its gcd after subtraction of `2^r` gives exactly
K7, including the equal-valuation cases. Every other noncentral weight is
divisible by that power of two: for even `r`, odd `r`th powers are `1`
modulo it, while even `r`th powers vanish. Their nonconstant finite
differences therefore vanish. The two singleton classes are present whenever
`m>=1`, so they also prove the converse gcd bound for the weights actually
present, not merely an infinite list of formal classes.

### Center congruence, exact finishing totals and uniformity

Greedy bulk balancing uses two primes on opposite sides of the mean. A step
opposes the current discrepancy and has magnitude at most `W_r delta`;
the same bound survives any number of bulk variables. No loss proportional
to the number of line constraints is hidden in that argument.

The center is chosen modulo **`2D_r`**, which is necessary for two lists
of odd primes. The specified class is odd, hence reduced, because the bulk
weights and the finishing weights are even. The power-of-two gcd result
therefore makes this an admissible prime progression. Choosing only modulo
`D_r` would not suffice.

After dividing the exact congruence by `2D_r`, the two-list completion is a
genuine integer solution. The inverse of `b/D_r` modulo `a/D_r` exists
when that modulus exceeds one. When it equals one, selecting an ordinary
nearest integer is the correct separate case. Nearest selection gives
`|S_b-m mu|<=a/D_r`; substitution into the exact weighted total gives K17
for the other list. Both list totals have parity `m`. The bound K18 is
more than enough to put both list centers within `delta/4` of `mu`.
It is legitimate to arrange K18 by increasing `M_r`: the stipulated
lower bound on `m` grows with `mu`, and `r` is fixed first.

Only two finishing lists are used, with one list at `r=1`. Their length is
`m`, not the larger side length. The count of target variables may grow
with `m`; the proof needs no prime-pattern theorem with that many forms.
Bulk values may repeat, and FL explicitly permits repeated target values.
None of these repetitions identifies or reuses array entries.

### The imported finite-list and prime-counting hypotheses

The reproduced FL interface agrees with the pinned source: its list-length
bound is `54000 ell^11`; its radius lies between `2^20 ell^11` and
one quarter of its actual center; the strong count is for the original
modulus, and the weaker count is needed for **all** auxiliary moduli through
`128 ell^2`. I checked its finite proof as well as its statement, including
the repeated target-pair prefix, total slot count, CRT lifts with overlapping
prime powers, and final complete-grid repair. Repetition is used only in
target lists, where it is allowed.

For the present application, `beta=71/120` and `epsilon=1/240` leave the
strict power gap `1/240` above the printed `7/12+epsilon` bound. This
absorbs the fixed interval factor and the cubic logarithm uniformly over
the required intervals and moduli. The fixed center modulus `2D_r` also
enters that auxiliary range eventually. For each shifted finishing center,
`ell_i<=ceil(log_2 mu)+1`; the 60000 constant in K11 pays the actual 54000
bound. The full radius interval lies in the local counting window. The
weighted prime lower bound, divided by the maximum logarithm in that
window, is stronger than both count hypotheses of FL. The conversion is
uniform, and the threshold remains ineffective.

Thus KW is uniform in `m,T` subject to its displayed hypotheses for each
fixed `r`. For the exact first-prime pool, PNT and partial summation give
K19; the total is odd, and `m/(log mu)^11` diverges on the entire odd tail.
The final window is smaller than `mu^(3/5)`. Every resulting prime is
eventually larger than every permitted gap modulus, which proves the
simultaneous unit assertion in KPT. This does not assert prescribed residues
for arbitrary user-supplied target tensors, an integer lift at small order,
or a permutation of the pool.

## Resource estimates

### Ladder and quantifier order

The choice `a_j=3/5+3j/[20(D+1)]` works for every finite depth fixed before
`n`. The strict adjacent gap may become small as `D` increases, but remains
positive at each fixed depth. Its endpoint is always below `3/4`.
Direct comparison with `X asymptotic k n^k log n` gives every R4 inequality.
In particular, the two most restrictive endpoint comparisons both have gap
`4/5-a_D>1/20`; the bundle fluctuation and random unused completion have
the separate positive gaps stated in the manuscript. The rounding term
`g n^(k-1)` is smaller than each `K_j X` by a power at least `8/5`, up
to logarithms. The prime-target window is `o(X)` for every `k>=2`.

This proves a symbolic fixed-depth ledger, rather than extrapolating a finite
decimal list. It neither supplies an admissible depth for an unproved
controller nor supports growing dimension. The full threshold is allowed
to depend on every fixed geometric constant and tuple size.

### Actual fresh values under the full deletion allowance

The initial seed supply uses consecutive disjoint prime pairs, so its
matching is real rather than a bounded-gap infinitude assertion. In the
middle-half interval there are asymptotically `X/(2 log X)` primes.
The total disjoint-pair gap is at most `X/2`, giving a positive fraction
with gap at most `8 log X`; pigeonholing the gap and then its reduced
lower class gives the claimed `X/log^3 X` order of matching supply.
Its endpoints exceed the selected gap. The whole seed invoice is smaller
by a power of `n`.

For later stages the narrow interval length has limiting power
`1-1/(5k)>=9/10` relative to `X`. The cited progression input therefore
applies with ample strict slack and growing modulus `g=O(log X)`.
Deleting **all** endpoints allowed by R6 still removes only a vanishing
fraction from any currently requested interval and reduced class. This
pays concentrated deletions, not merely average deletions. The fixed
constant `F=ceil(100 log X)` is sufficient for the growth step: applying
the uniform asymptotic to the full middle-half interval gives more than
`X/(8g log X)` fresh members after eventual deletion, which exceeds
`X/(gF)`.

The grouped growth lemma is valid for every fixed finite `M`. In a dense
bin the spacing lower bound controls the number of very short pairs;
the remaining quadratic number of pairs yields the claimed repeated
difference. Its fixed-difference graph has degree at most two, so a
matching with the required number of edges exists. The constants
`B_M=256(M+1)` and `P_M` pay both the seed count and multiplicative
growth. Differences are multiples of the common gap and at most the
current complete-grid endpoint, so the grid extends without holes.
No analytic theorem on the much smaller growth-bin intervals is being
silently invoked.

For macro stages, the two separated narrow intervals and same-class
pigeonhole give the repeated-difference count R9. At a fixed difference,
each lower and upper endpoint has only one partner, so the resulting pairs
are already disjoint. The count diverges uniformly over the allowed gaps
and exceeds any fixed `M`. Opposite unit classes `-1,+1` give the residue
stages with difference `2 mod g`, including the case `g=2`. Every allocated
endpoint lies in the exact initial-prime pool and is removed before the
next request. Prefix endpoints need not be centered, and their full cost
is retained separately.

Appending the prescribed macro count preserves the complete grid and gives
total scalar range at least `8K_j X`. The selected central subset and its
complement are both legal states, differ by at most one gap, and each has
the claimed signed capacity. This is stronger than a gcd statement.
Its physical use still requires a separately proved simultaneous switch
geometry with distinct cells and the stated complete line signature.

### Joint centering and the changed unused mean

JC correctly randomizes complete reservoir reference states. Its hypotheses
give a bounded line-contribution range for each entire independent variable;
individual cells or individual pairs are not assumed independent. Macro
cells have their actual pair midpoint as expectation, while the prefix and
fixed residue cells are charged at the full `X` scale. The number of
independent reservoirs meeting a line is bounded by its reserved cell count.
Hoeffding and the full line inventory therefore give R11 simultaneously.

Summing R11 over one axis partition is the necessary accounting step. It
counts each reserved entry once and gives the exact unused-mean error
bound R12. The expected completed line consequently has error at most
`3E`, rather than retaining the original pool mean without justification.
For the uniform remaining bijection, the displayed sampling-without-
replacement martingale has differences bounded by `X`, yielding R13.
The union-bound choice of `u` controls every full signed line, even those
outside a later target family. RL makes `E+u=o(K_0 X)`.

The argument preserves the exact pool: the fresh reserved assignment is
injective, and unused cells receive a bijection of precisely its complement.
It retains the scalar capacities because the chosen whole reference states
were the two legal central states. **These conclusions are conditional on
JC's separate disjoint-placement, per-line occupancy and whole-bundle range
hypotheses.** Global reservation R6 alone does not establish any of them.

## Finite evidence and independent checks

The frozen author commands passed under Python 3.12.14:

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyperk_targets.py self-test
python3 -B problems/prime-arrays-beyond-square/code/hyperk_resources.py
```

The target test reported 152 independently enumerated weight entries, gcd
checks through degree 64, 3200 exact centered completions, eight finite
prime-target certificates and 56 rejected certificate corruptions. The
resource test reported 252 exact rational exponent cases and eight rejected
controls. These are finite implementation evidence, not analytic estimates
at any numerical threshold.

For the reviewer controls, extract the scientific revision into a fresh
directory and pass that directory to the reviewer program. For example:

```sh
mkdir /tmp/hyperk-targets-resources-review-source
git archive 5692d37633ef4b509e8429cddf4ed762e7235d08 | tar -x -C /tmp/hyperk-targets-resources-review-source
python3 -B problems/prime-arrays-beyond-square/reviews/hyperk_targets_resources_controls.py /tmp/hyperk-targets-resources-review-source
```

All added controls passed:

| Independent check | Result |
|---|---|
| Occupancy-state weight recurrence | 1227 weight entries agree with the author formulas; the recurrence does not use inclusion-exclusion. |
| Last-coordinate recurrence and gcd | Every weight and the full gcd agree through degree 128, including absent zero-containing classes and the unit center. |
| Exact rational finishing totals | 1600 additional completions; all parity, exact weighted sums and bounds checked; 1601 wrong-residue cases rejected. |
| Bulk balancing | 10000 nonuniform bounded-weight steps retain the uniform discrepancy bound. |
| Dimension-five retained input | Independently trial-divided first 3125 odd primes give total 42185933; 6841 geometric lines and 3570 two-parameter sections satisfy the target identities. |
| Dimension-six retained input | Independently trial-divided first 15625 odd primes give total 1271702185; 51012 geometric lines and 38971 two-parameter sections satisfy the target identities. |
| Corrupted target inputs | Fourteen independent corruptions rejected: composite, missing/duplicate labels, wrong total, omitted line count, multiset rule and false arrangement kind. |
| Further resource diagnostics | 186 exact fixed-dimension/depth cases, including exponential and million-level depths; three invalid endpoint exponents rejected. |
| Complete scalar grids | Nine exact grid and complementary-reference cases, including composite gaps 6 and 30; a gcd-only hole example is retained. |
| Grouped difference matching | A finite arithmetic-set example has the stated difference range and degree bound, with 384 disjoint pairs. It is not a finite prime-density assertion. |
| Unused-pool centering | All 240 completions of two actual reference states in the nine-prime pool verify the exact conditional mean and its bound. They are not all-prime-line arrays. |
| Dependence negative control | A shared switch has variance 64 where falsely independent cells would give 34; unchanged unused mean is also explicitly falsified. |

The geometric target checker constructs coordinate-function cell sets and
then independently partitions each two-parameter section in both directions.
It does not call the author's line enumeration, weight formulas, pool sieve
or partition checker. Its output deliberately records
`integer_lift_checked=false` and `arrangement_checked=false`.

At the majority-controller diagnostic depths, `k=5,D=9` gives
`a_D=147/200`, adjacent gap `3/200`, and deletion/centering slack `13/200`.
At `k=6,D=11` these are `59/80`, `1/80`, and `1/16`. The proof of the
general ladder is algebraic; these checks do not replace its fixed-`k`
quantifiers or assert an actual physical controller at an arbitrary depth.

I also ran `python3 -B check.py` in the delivery working tree after adding
these reviewer files. Integrity and all 45 tooling tests passed. This is a
local repository check and is separate from the mathematical verdict and
from remote CI.

## Disposition and remaining boundary

No scientific repair is required within this review's scope. One optional
precision improvement is to write `2<=g` explicitly in RL's statement:
positivity is already supplied by the surrounding prime-gap definition and
every application, but the displayed upper bound alone could be clearer.

The reviewed target construction supplies all signed two-block equations
and the exact pool total. The reviewed resource scheme pays any controller
that actually verifies its stated finite-depth geometric interface. Neither
result supplies a distributed full signed-kernel packing theorem. The
remaining physical bottleneck must retain its open status, and the full
all-dimension prime-permutation theorem must not be marked complete on the
strength of this review. No proof assistant, numerical analytic cutoff,
remote CI run or formal GitHub approval is part of this verdict.
