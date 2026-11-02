# Wider finite-list windows for the explicit signed cube

Public proof manuscript. See [provenance](../PROVENANCE.md#explicit-prime-cube) for the pinned sources, internal review and verification limits.

## 1. Finite cube hypotheses

For odd `n>=11`, retain the exact original entry pool and its actual total:


```math
A=\{p_2,\ldots,p_{n^3+1}\},\quad X=\max A,\quad T=\sum A,
 \quad m=T/n^3,\quad\mu=T/n^2=nm.
```


For an integer `b>=2` and a positive rational `rho`, put


```math
L=\log X,\quad e=\lceil\log_2(2nX)\rceil,
 \quad d=\mu/(\rho L^b).                                     \qquad\text{(Q1)}
```


Assume


```math
\begin{split}
 &n^3\le X,\quad X/4\le m\le X,\quad L\ge2,
       \quad\rho L^b\ge16,\\
 &n\ge680e^{11},\qquad d\ge2048e^{11}.                        \qquad\text{(Q2)}
 \end{split}
```


Fix any even `2<=g<=16ceil(log2 X)`. For every center


```math
y\in[\mu-2d,\mu+2d],\qquad\ell=\lceil\log_2y\rceil,          \qquad\text{(Q3)}
```


assume every interval `I` inside `[y-d,y+d]` of length at least `d/2`
has these two supplies:


```math
\pi(I;g,a)\ge |I|/(4g\ell)
       \quad\text{for each reduced }a\pmod g,                 \qquad\text{(Q4)}
```



```math
\pi(I;h,a)\ge |I|/(4h\ell^9)
 \quad\begin{array}{l}
 \text{for each even multiple }h\text{ of }g\text{ with }h\le8g\ell,\\
 \text{and each reduced }a\pmod h.
 \end{array}                                                  \qquad\text{(Q5)}
```


A theorem for all moduli at most `128ell^2` suffices for (Q5), but TQ
uses only the selected even multiple of `g`. These are line-sum targets,
so earlier target values are not deleted. All entries of `A` remain a
separate distinct pool for the physical controller.

The actual local bounds, including the finishing and face centers, are


```math
\frac{7\mu}{8}\le y\le\frac{9\mu}{8},\quad
 X\le nX/8\le y\le2nX,\quad
 \lceil\log_2X\rceil\le\ell\le e,\quad d\le y/4.              \qquad\text{(Q6)}
```


The weaker `y>=mu/2>=nX/8` gives the middle inequality. The sharper
`7mu/8` is retained for the analytic domain. No local center is silently
replaced by `mu` or by `X`.

## 2. The complete finite TQ lemma

Let `y,D>0`, `ell=ceil(log2 y)>=2`, and integer `F>=1`. Let `g`
be even, `2<=g<=16ell`, and let `a_1,...,a_k` be reduced classes
modulo `g`. Suppose


```math
ky\in\mathbb Z,\quad\sum_i a_i\equiv ky\pmod g,\quad
 D\le y/4,\quad D\ge512F\ell^2,\quad
 k\ge8\ell\{3F(4\ell+6)+7\}.                                 \qquad\text{(Q7)}
```


Suppose intervals inside `[y-D,y+D]` of length at least `D/2` have
at least `|I|/(4gell)` primes in each reduced class modulo `g`, and
at least `|I|/(hF)` primes in every reduced class modulo every even
multiple `h` of `g` satisfying `h<=8gell`. Then there are primes,
with repetitions allowed, such that


```math
t_i\equiv a_i\pmod g,\qquad|t_i-y|\le D,\qquad
 \sum_i t_i=ky.                                               \qquad\text{(Q8)}
```


### Seed and reduced lift

One original class occurs at least `k/phi(g)` times. Since `g` is
even, `phi(g)<=g/2<=8ell`. In the central interval
`[y-D/4,y+D/4]`, of length `D/2`, its supply is
`M_0>=D/(8gell)>=4F`. Consecutive members have some gap


```math
h\le D/M_0\le8g\ell\le128\ell^2.                            \qquad\text{(Q9)}
```


The span is at most `D/2` and `M_0-1>=M_0/2`. The gap is a
positive even multiple of `g`. For this seed pair `(r,s)`, the
lower prime exceeds `h`: `y-D/4>=15D/4`, and `D>=4Fh`.
Thus `c=r mod h` is a reduced lift of the selected original class.

### Fine grid through 2D

Let `B` be the primes in class `c mod h` inside `[y-D/2,y+D/2]`;
its size `M` is at least `D/(hF)>=4`. Use `4F` copies of the seed
pair to cover all `h`-multiples from zero to `R_0=4Fh`, where


```math
4D/M\le R_0\le D.                                           \qquad\text{(Q10)}
```


For `R_0<=R<D`, divide the already counted interval into at most
`ceil(D/R)<=2D/R` bins. One contains at least `MR/(2D)>=2`
points. Its extremes give an `h`-multiple `w` satisfying


```math
R/(4F)\le hMR/(4D)\le w\le R.                               \qquad\text{(Q11)}
```


Here the span of `z>=2` points in one class is at least `h(z-1)>=hz/2`.
Appending the pair preserves complete grid coverage, since the old
grid and its translate by `w<=R+h` touch or overlap. Each block of
`4F` extensions at least doubles the endpoint by the binomial theorem.
At most `4Fell` stages reach `R>=D`, because `D<=y<=2^ell`;
the endpoint at first passage is less than `2D` unless `R_0=D`.

The two extremes of `B` have difference


```math
D/(2F)\le hM/2\le h(M-1)\le w_0\le D.                       \qquad\text{(Q12)}
```


At most `2F` further copies reach `R>=2D`; their use is legal
because `w_0<=D<=R`. The final endpoint is less than `3D`, and
the total prefix length satisfies


```math
P\le F(4\ell+6).                                            \qquad\text{(Q13)}
```


All prefix endpoints stay within `D/2` of `y`. The smaller bins in
this argument are not new analytic requests; they partition an already
supplied finite set.

### Wide capacity and two free coordinates

Choose primes of class `c` from `[y-D,y-D/2]` and `[y+D/2,y+D]`.
Each bracket has lower count `D/(2hF)>=2`. Their difference is in
`[D,2D]` and midpoint within `D/4` of `y`. Append `J=2P+5`
copies, legal because the fine grid already reaches `2D`. The
`r_*=P+J=3P+5` controlled slots cover the entire `h`-grid in
`[A_*,A_*+R_*]`, where `A_*` sums their lower endpoints and


```math
R_*\ge JD,\qquad|A_*+R_*/2-r_*y|\le PD/2+JD/4.                \qquad\text{(Q14)}
```


The chosen original class has at least
`k/(8ell)>=3F(4ell+6)+7>=r_*+2` coordinates. Reserve `r_*`;
at least two coordinates remain free.

Lift every unreserved original class to a unit modulo `h`, with their
sum equal to `ky-r_*c mod h`. Compatibility modulo `g` already holds.
At an old prime power `p^v||g`, possibly with higher exponent
`p^w||h`, adjust one lift by a multiple of `p^v` to correct the sum
modulo `p^w`, preserving its unit property. A new prime dividing `h`
is odd because `g` is even. After fixing other coordinates, any residual
`z mod p^w` is a sum of two units: choose the first modulo `p`
outside `{0,z}`, and set the second by the sum. A choice exists even
at `p=3`. CRT combines the prime-power choices, without assuming
`g` and `h/g` coprime.

### Exact sum

For each unreserved lifted class take lower/upper bracket primes, choosing
the lower if the running discrepancy is nonnegative and the upper otherwise.
The discrepancy stays in `[-D,D]`, independently of the list length.
The desired controlled sum is congruent to `A_* mod h` and differs
from its interval midpoint by at most


```math
D+PD/2+JD/4\lt JD/2\le R_*/2,                                  \qquad\text{(Q15)}
```


since `J=2P+5` gives strict slack `D/4`. It is therefore a covered
grid point. Choose an endpoint in each controlled slot to attain it.
This proves (Q8), with its exact total and all original residues.

### The specialization consumed here

Take the integer `F=4ell^9`. Then (Q5) is precisely the density used
by TQ, and the radius condition is `D>=2048ell^11`. The exact list
condition is bounded by


```math
384\ell^{11}+576\ell^{10}+56\ell\le680\ell^{11}
       \qquad(\ell\ge2),                                    \qquad\text{(Q16)}
```


because `384+288+56/2^10<680`. Thus (Q2),(Q6) pay every literal
TQ size and modulus condition at each shifted center, with `k=n`.
No stronger weak analytic density is presumed.

## 3. Complete cube target composition

Fix any symmetric matrix of units modulo `g` with labeled total `T mod g`.
For each non-diagonal two-element symmetry orbit, (Q4) supplies a lower
prime in `(mu-d,mu-d/2]` and an upper prime in `(mu+d/2,mu+d]`.
Their lower count is at least
`d/(8g ell_mu)>=2048e^11/(128e^2)=16e^9>1`.

Assign one prime to both positions of each orbit. Its weight is exactly
two. Choosing a prime whose sign of displacement opposes the accumulated
weighted discrepancy keeps that discrepancy `E` in `[-2d,2d]`.
The remaining exact integer total is


```math
T'=T-\sum_{i\ne j}P_{ij}=n\mu-E,\qquad y'=T'/n=\mu-E/n.       \qquad\text{(Q17)}
```


Exactly the **`n` diagonal positions** remain. Their prescribed classes
sum to `T' mod g`, and `|y'-mu|<=2d/n<d/4`. Apply the just-proved
TQ lemma to these `n` positions at center `y'`, radius `d`, and
integer total `T'`. The center belongs to (Q3); equations (Q2),(Q6)
and (Q16) check every size/modulus hypothesis. The prime requests in
(Q4),(Q5) extend down to the actual `d/2` required by TQ.

The resulting symmetric matrix of primes has total `T`, the desired
residues, and


```math
|P_{ij}-\mu|\le(1+2/n)d.                                    \qquad\text{(Q18)}
```


Use it as the axis-target matrix in each of the three directions, with
the remaining coordinates in their natural order. The same row and
column sums of a symmetric matrix appear on both sides of every plane
identity. Hence all axis marginal equations hold, and every directional
total is the exact pool total `T`.

Form the odd section totals


```math
S_+=\sum_iP_{ii},\qquad S_-=\sum_iP_{i,n-1-i}.                \qquad\text{(Q19)}
```


For each of the six face families, select any `n` unit residues summing
to the appropriate `S_+` or `S_- mod g`, and apply TQ separately
at that total divided by `n`. The center differs from `mu` by at most
`(1+2/n)d`, so again belongs to (Q3). This produces exactly the six
required integer family totals. Every resulting face target satisfies


```math
|t-\mu|\le(2+2/n)d.                                         \qquad\text{(Q20)}
```


The totals may be composite and nonunits modulo `g`. They are not
the individual unit targets to which the progression theorem is applied.
Repeated prime target values, within or between families, are permitted.

For each body line, take a prime in any specified unit class modulo `g`
from a bracket within `d` of `mu`, using (Q4). There are four such
independent choices. The retained signed incidence theorem for odd
`n>=11` has no further body relation. Its six face identities are
exactly the six totals verified above. This does not infer an integer
image statement from rational rank.

Admissible residue prescriptions exist for every allowed `g`. Every
odd residue modulo an even modulus is a sum of three units: at an odd
prime power take the first to be `1`, choose the second outside `0`
and the residue making the third zero modulo that prime, and set the
third by the sum. At the power of two choose odd summands; CRT
combines them. Set `n-3` positions to `1` for a face list. For
the symmetric axis pattern set all positions except three diagonal
positions to `1`. The remaining residue is odd because `T` is odd.
The construction includes `g=2`; it does not require a section total
to be prime or coprime to `g`.

**Theorem QST (finite TQ signed targets).** Under (Q1)--(Q5), every
admissible symmetric axis residue pattern, every admissible set of six
face residue lists selected after that matrix, and every four unit
body residues admit compatible prime targets for all `3n^2+6n+4`
full signed-coordinate lines. Their maximum displacement from `mu`
is at most `(2+2/n)d`. Repetition of target values is allowed. The
entry pool is exactly the original `A`; no target is added as an entry.

## 4. Exact analytic request conversion

Use the separately proved effective interval theorem with its actual
denominator parameter. At center `Y` with `u=log Y>=U`, suppose
intervals inside `[Y/2,2Y]` of length at least `Y/(kappa u^s)`
have strong count `H/[2phi(q)log(2Y)]` for `q<=64u` and weak
count `H/[4q ceil(log2Y)^9]` for `q<=512u^2`. Here `s>=b`,
and `kappa` is a positive integer within the analytic theorem's proved
parameter domain. The primitive-conductor and exceptional-zero budgets
remain part of that separate theorem.

At a target center (Q3), `u>=L`, `y>=7mu/8`, and `y<=mu+2d`.
The sufficient domain and length conditions are


```math
\log(7\mu/8)\ge U,\qquad
 \kappa L^{s-b}\ge2\rho+\frac4{L^b}.                          \qquad\text{(Q21)}
```


Indeed


```math
H\ge\frac d2=\frac{\mu}{2\rho L^b}
 \ge\frac{\mu(1+2/(\rho L^b))}{\kappa L^s}
 \ge\frac y{\kappa u^s}.                                     \qquad\text{(Q22)}
```


Since `d<=y/4`, all local intervals lie inside `[y/2,2y]`. The
pointwise bounds `log2>2/3` and `u>=L>=2` give


```math
\ell\le2u,\qquad128\ell^2\le512u^2,
 \qquad g\le32u\lt 64u.                                        \qquad\text{(Q23)}
```


Thus the weak estimate implies (Q5) for every selected even multiple
and every lifted reduced class. The strong estimate implies (Q4),
since `phi(g)<=g` and `log(2y)<=2ell`. Closed bracket counts in
TQ inherit the half-open analytic count. All centers and endpoints
are within the literal source domain; none is replaced by a nominal
global scale.

When `s=b`, (Q21)'s window test is exactly


```math
(\kappa-2\rho)L^b\ge4.                                     \qquad\text{(Q24)}
```


For `rho=101/100,b=s=16`, the integer choice `kappa=3` reduces
this to `L^16>=200/49`, already implied by `rho L^16>=16`.
The frozen FL construction at the same radius needs `kappa=506`.
The reduction to 3 follows from the new complete proof above; it
does not weaken an FL hypothesis.

No prime theorem is requested in the small bins used for complete-grid
growth. The actual analytic requests are only the following.

| Request | Modulus | Minimum interval length |
|---|---|---:|
| Outer symmetry-orbit bracketing | `g`, prescribed class | `d/2` |
| TQ seed | `g`, selected frequent class | `d/2` |
| TQ prefix stock | selected even `h`, one reduced class | `d` |
| Wide pairs and free-coordinate brackets | selected `h`, required reduced classes | `d/2` |
| Four body choices | `g`, prescribed classes | `d/2` suffices |

## 5. Scaled controller capacities and the sharp target radius

Let `lambda0>0` be a rational controller multiplier and let


```math
K_0=\left\lceil\lambda_0 n/L^{a_0}\right\rceil,
       \qquad b\ge a_0\ge0.                                 \qquad\text{(Q25)}
```


If explicit estimates give `m<=MX` and `n>=N>=11`, then


```math
\frac{\max_\lambda|t_\lambda-\mu|}{K_0X}
 \le\frac{(2+2/N)M}{\rho\lambda_0 L^{b-a_0}}.                 \qquad\text{(Q26)}
```


This is pointwise in the actual ceiling. It does not require a
monotonicity assertion about the rounded `K0`.

For `M=501/1000,N=200` and `rho*lambda0=101/100`, with `b=a0`,
the bound is


```math
\frac{100701}{101000}\lt 1.                                    \qquad\text{(Q27)}
```


The exact `(2+2/n)d` bound is essential at this radius. The coarser
`3d` estimate would not establish the same controller inclusion.

Two parameter profiles are recorded separately:

| Profile | `lambda0` | `a0=b=s` | `rho` | Analytic integer `kappa` |
|---|---:|---:|---:|---:|
| TQ with unscaled logarithmic controller | `1` | `16` | `101/100` | `3` |
| TQ with a smaller controller multiplier | `2^-161` | `5` | `(101/100)2^161` | `3*2^161` |

Both have the same product `rho*lambda0` and hence the same exact
target/controller ratio. The second pays its smaller target radius in
the `rho` factor of every size and analytic condition; it does not
pretend to use `kappa=3`. Its window condition is
`(49/50)2^161 L^5>=4`.

The weighted profile is a finite target-interface consequence. A complete
cutoff using it additionally requires a new physical-controller parameter
proof and an analytic theorem covering its stated large fixed integer
denominator. Neither is inferred from the unscaled profile or from this
target calculation. Both remain explicit global-composition obligations.

## 6. Complete algebraic tail, with ceiling jumps paid pointwise

Assume the independent prime estimates have established `n^3<=X<=n^4`
and `m>=X/4`. Put `v=log2 n`. For every real `v>=2`,


```math
2v\le L\le4v,\quad e\le6v,\qquad
 d\ge\frac{2^{4v}}{4\rho(4v)^b}.                             \qquad\text{(Q28)}
```


The literal TQ size conditions follow from


```math
2^v\ge680(6v)^{11},\qquad
 2^{4v}\ge2^{13}\rho(4v)^b(6v)^{11}.                         \qquad\text{(Q29)}
```


The first envelope first succeeds at the integer `v=113`. For the
unscaled profile the radius envelope first succeeds at 58. Both
profiles in the preceding table satisfy both tests at `v=113`,
including the full `rho` factor in the weighted profile.

The logarithmic derivatives of the two left/right ratios are respectively
`log2-11/v>2/3-11/v` and
`4log2-(b+11)/v>8/3-(b+11)/v`, positive throughout `v>=113`.
Relative-radius and order conditions increase with the lower logarithm
bound `2v`. For `s>=b`, the left side minus the right side of
(Q21)'s length inequality increases with `L`; for `b>=a0`, the
box ratio (Q26) does not increase. These establish the whole real tail.
The ceiling bounds for `e` and `K0` are pointwise at every order,
so no rounded-monotonicity step is hidden.

The value `2^113` is only a target algebra floor, not a cube cutoff.
The analytic starting domain is still `log(7mu/8)>=U`. In particular,
if the independent mean bound gives `m>=12X/25`, its literal lower
center is `(21/50)nX`, so


```math
\log(7\mu/8)\ge\log X+\log n+\log(21/50).                   \qquad\text{(Q30)}
```


A smaller complete cutoff must be obtained by reevaluating every analytic,
geometric, deletion, centering, residue and correction condition in the
global composition. No component improvement is itself a claimed new
complete record.

## 7. Replay and preservation

The standard-library checker `code/verify_explicit_signed_targets_tq.py`
binds the frozen TQ proof, pays the exact rational profile (including
`rho` and `lambda0`), verifies its list/radius conditions, center shifts,
sharp box ratio and whole-tail derivative guards. Negative controls
include using `n^2` finishing slots, the preceding unsupported algebra
floor, an interval denominator that omits the shift, a missing controller
multiplier, an unpaid target radius, and nonexact numeric inputs.

The recovered finite TQ program was inspected and replayed: 201 targets,
mean 100003, radius 20000, exact total 20100603, original modulus 6,
lifted modulus 30. Its 20 prefix and 45 wide slots control 65 positions;
all 14 distinct target primes are independently trial-divided. It checks
798 CRT cases, exhausts 14 grid points, and rejects 13 damaged examples.
Those are finite mechanism checks, not proofs of analytic supplies.

The new proof retains all six exact family totals, four bodies, the
three-unit original residue construction, the two-free-coordinate lifted
CRT step, and the exact input pool. The original FL files, their source
hashes, and every earlier complete cutoff remain separate checkpoints.
Arithmetic acceptance is distinct from analytic proof, independent review,
kernel verification, remote CI, external acceptance and integration.
