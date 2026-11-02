# A cheaper exact-total prime-target reservoir

## Scope and status

These manuscript-local results are additive to
[the preserved target lemma](../explicit-targets.md), whose proof and
inputs are unchanged. The present argument is a finite, conventional proof
under explicit prime-supply hypotheses. Its arithmetic and finite controls
are checked by [the accompanying program](../PROVENANCE.md#optimized-bound).
The program does not establish the analytic supply hypotheses or a theorem
about squares. Independent review and the exact reviewed source revision
are recorded separately by the coordinator.

The changes remove unnecessary narrow intervals, repeated wide pairs, and
two powers of padding from any unchanged analytic density. A stronger
analytic density can be substituted through the integer parameter `F`.
Repeating target primes remains legitimate because they are line sums, not
entries in the prescribed pool. No array entry is duplicated.

## TQ: finite target lemma with a density parameter

Let `y,D>0`, let `ell=ceil(log_2 y)>=2`, and let `F>=1` be an integer.
Let `g` be even with `2<=g<=16ell`. Let `a_1,...,a_k` be reduced classes
modulo `g`, with `T=ky` an integer and `sum a_i=T (mod g)`. Assume


```math
D\le y/4,\qquad D\ge512F\ell^2,\qquad
 k\ge8\ell\{3F(4\ell+6)+7\}.                         \qquad\text{(TQ.1)}
```


Assume that every real interval `I` inside `[y-D,y+D]`, with length at
least `D/2`, has the following prime supplies:

* in each reduced class modulo `g`, at least `|I|/(4g ell)` primes;
* in each reduced class modulo every even `h` that is a multiple of `g`
  and satisfies `h<=8g ell`, at least `|I|/(hF)` primes.

It suffices for the second statement to hold only for the single `h`
selected in Step 1, provided the analytic theorem guarantees it regardless
of that selection. In particular a uniform theorem for `q<=128ell^2`
is sufficient; the construction does not request all those moduli at once.
An interval count for `(b,c]` also supplies the corresponding closed interval.

Then there are primes `t_i`, with repetitions permitted, satisfying


```math
t_i\equiv a_i\pmod g,\quad |t_i-y|\le D,\quad
 \sum_i t_i=T.                                          \qquad\text{(TQ.2)}
```


### 1. Seed pair and the original residue class

There are `phi(g)` available reduced classes, so one original class `a`
occurs at least `k/phi(g)` times. Since `g` is even,
`phi(g)<=g/2<=8ell`. The central interval
`[y-D/4,y+D/4]` contains `M_0>=D/(8g ell)>=4F` primes in this class.
Among consecutive members some pair `(r,s)` has


```math
h=s-r\le D/M_0\le8g\ell\le128\ell^2.                 \qquad\text{(TQ.3)}
```


Indeed the total span is at most `D/2` and `M_0-1>=M_0/2`.
The difference `h` is a positive even multiple of `g`. The lower endpoint
of the central interval is at least `15D/4>h`, since `D>=4Fh`.
Thus `b=r mod h` is reduced and lifts `a mod g`.

### 2. A complete fine grid up to length D

Let `A` be the primes congruent to `b mod h` in
`[y-D/2,y+D/2]`. Its size satisfies `M>=D/(hF)>=4`.
Use `4F` copies of `(r,s)`. The possible increments are exactly all
`h`-multiples from zero through `R_0=4Fh`, with


```math
4D/M\le R_0\le D.                                     \qquad\text{(TQ.4)}
```


As in the preserved finite binning argument, if `R_0<=R<D`, divide the
interval of length `D` containing `A` into `ceil(D/R)<=2D/R` bins of
length at most `R`. One bin contains at least `MR/(2D)>=2` points.
Its extreme difference is an `h`-multiple `d` satisfying


```math
R/(4F)\le hMR/(4D)\le d\le R.                         \qquad\text{(TQ.5)}
```


The middle bound uses the grid spacing `h` and `z-1>=z/2` for a bin
with `z>=2` points. Appending this pair extends a complete `h`-grid
from `[0,R]` to `[0,R+d]`, because `d<=R+h`. The two intervals of
grid points touch or overlap. A group of `4F` such extensions at least
doubles `R`, since `(1+1/(4F))^(4F)>=2`. At most `4F ell` extensions
therefore reach `R>=D`: `D<=y<=2^ell` and `R_0>=1`.
At first passage, `D<=R<2D`, unless already `R_0=D`.

### 3. Extend the fine grid to 2D without requesting narrower windows

Let `(u_0,v_0)` be the two extreme members of `A`, with difference `d_0`.
Since `M>=4`,


```math
D/(2F)\le hM/2\le h(M-1)\le d_0\le D.                \qquad\text{(TQ.6)}
```


Starting from `R>=D`, append copies of this pair until `R>=2D`.
Every extension is legal because `d_0<=D<=R`. At most `2F` copies
are needed, and the resulting endpoint is less than `3D`. The total
prefix length `P` thus satisfies


```math
P\le4F(\ell+1)+2F=F(4\ell+6).                         \qquad\text{(TQ.7)}
```


All prefix endpoints remain in `[y-D/2,y+D/2]`. In particular the sum
of their pair midpoints differs from `Py` by at most `PD/2`.
The sole purpose of extending the fine grid to `2D` is to permit wider
later windows while retaining complete coverage.

### 4. Wide capacity at a fraction of the old slot cost

The supply hypothesis gives a prime `u=b (mod h)` in `[y-D,y-D/2]`
and a prime `v=b (mod h)` in `[y+D/2,y+D]`. Each window has length
`D/2`; its lower count is `D/(2hF)>=2`. These primes satisfy


```math
D\le v-u\le2D,\qquad |(u+v)/2-y|\le D/4.             \qquad\text{(TQ.8)}
```


Append `J=2P+5` copies of this pair. Their differences are at most `2D`,
so all extensions are legal after Step 3. With `r_*=P+J=3P+5`,
let `A_tot` be the sum of all lower endpoints and `R_tot` the total
difference. Every `h`-grid point of `[A_tot,A_tot+R_tot]` is realized, and


```math
R_{\rm tot}\ge JD,\qquad
 |A_{\rm tot}+R_{\rm tot}/2-r_*y|\le PD/2+JD/4.         \qquad\text{(TQ.9)}
```


By (TQ.1), the common original class has at least


```math
k/\varphi(g)\ge k/(8\ell)
 \ge3F(4\ell+6)+7\ge r_*+2                            \qquad\text{(TQ.10)}
```


coordinates. Reserve `r_*` of them. There are at least two unreserved
coordinates, including at least two of this common class.

### 5. Two free coordinates suffice for the congruence lift

Lift every unreserved original class to a reduced class `b_i mod h`,
requiring their sum to be `T-r_*b mod h`. The target sum is already
compatible modulo `g`. For every prime power `p^v||g`, `p^w||h`, alter
one lift by a multiple of `p^v` to set the sum modulo `p^w`; its residue
modulo `p` remains nonzero. For every new prime `p|h`, `p` is odd
because `g` is even. Fix arbitrary units for all but two coordinates.
Given the residual sum `c mod p^w`, choose the first coordinate modulo
`p` outside `{0,c}`. At least one choice exists since `p>=3`; set the
second equal to `c` minus the first modulo `p^w`. Both are units.
The Chinese remainder theorem combines these prime-power choices.
This explicitly covers overlapping prime powers; no coprimality of
`g` and `h/g` is assumed.

### 6. Bounded discrepancy and the exact sum

For each unreserved lifted class choose one lower prime in
`[y-D,y-D/2]` and one upper prime in `[y+D/2,y+D]`.
If the running discrepancy from the mean is nonnegative choose the lower
prime; otherwise choose the upper. Induction keeps the total discrepancy
within `[-D,D]`, independently of the number of free coordinates.

The desired sum for the reserved coordinates is congruent to `A_tot mod h`.
Its distance from the controlled midpoint is at most


```math
D+PD/2+JD/4 < JD/2\le R_{\rm tot}/2,                  \qquad\text{(TQ.11)}
```


because `J=2P+5` and
`J/4-(1+P/2)=1/4>0`. It is therefore a covered grid point, realized
by choosing an endpoint in every controlled slot. This proves (TQ.2).

## Exact analytic request ledger

No subinterval shorter than `D/2` occurs in this proof.

| Purpose | Modulus/class | Requested interval | Length |
|---|---|---|---|
| Seed selection | `g`, one selected original class | `[y-D/4,y+D/4]` | `D/2` |
| Prefix set A | selected `h`, selected class `b` | `[y-D/2,y+D/2]` | `D` |
| Wide pair and free lower brackets | selected `h`, required reduced classes | `[y-D,y-D/2]` | `D/2` |
| Wide pair and free upper brackets | selected `h`, required reduced classes | `[y+D/2,y+D]` | `D/2` |

The finite binning step applies to already supplied `A`; it invokes no prime
theorem in its small bins. Selecting a bin and reusing endpoint primes has
no entry-depletion cost. The fine-grid extension also uses only `A`.

For a real density cost `F_0>=1`, set `F=ceil(F_0)` and use (TQ.1)
with this integer. This keeps all complete-sequence multiplicities integral;
no differentiability argument across a ceiling is needed.

## Polynomial specializations and what they do not establish

If a supplied analytic theorem gives a density at least
`|I|/(4q ell^s)` for some integer `s>=2`, take `F=4ell^s`.
For `ell>=2` a convenient sufficient specialization is


```math
D\ge2048\ell^{s+2},\qquad k\ge680\ell^{s+2}.          \qquad\text{(TQ.12)}
```


Indeed the exact list requirement becomes
`384ell^(s+2)+576ell^(s+1)+56ell`, whose ratio to `ell^(s+2)`
is at most `384+288+28=700` for `s=0`; for `s>=1` it is at most
`384+288+14=686`; and for **s>=2** it is at most
`384+288+7=679<680`. Thus (TQ.12) is stated and used only for `s>=2`.
For smaller `s`, retain the exact formula (TQ.1), or use coefficient 700.

| Supplied density | Original / optimized size powers | Optimized sufficient conditions |
|---|---|---|
| Baseline lemma `1/(4q ell^9)` | 11 / 11 | `D>=2048ell^11`, `k>=680ell^11` |
| Actual baseline weak consequence `1/(4q ell^7)` | 11 / 9 | `D>=2048ell^9`, `k>=680ell^9` |
| New density `1/(4q ell^3)`, if proved | 11 / 5 | `D>=2048ell^5`, `k>=680ell^5` |
| New density `1/(4q ell^2)`, if proved | 11 / 4 | `D>=2048ell^4`, `k>=680ell^4` |

The baseline weak interface implies the second row because its denominator
`2phi(q)(log y)^6 log(2y)` is at most `4q ell^7`.
The last two rows are interface consequences, not independent claims that
those analytic supplies hold. They require a separately proved analytic
interface and its full domain checks.

For the candidate analytic cost


```math
F=\ell\{7+2\lceil\log_2\ell\rceil\}^2,                 \qquad\text{(TQ.13)}
```


the exact formula (TQ.1) applies directly. The simpler bound `F<=4ell^2`
holds for every integer `ell>=256`. At `ell=256`, the squared factor
is `23^2<=1024`. On any subsequent integer bin
`2^(j-1)<ell<=2^j`, with `j>=9`, it is at most `4ell` because
`(7+2j)^2<=2^(j+1)`. The latter begins with `25^2<=2^10`, and persists
under `j -> j+1`: writing `a=7+2j>=25`, `(a+2)^2<=2a^2` follows
from `a^2-4a-4>0`. This proof explicitly covers each ceiling jump.
Consequently the `s=2` row applies to (TQ.13) throughout that integer tail.

For the square application's `D=y/ell^4`, the widest required interval is
still contained in `[y-D,y+D]`. Since `ell<=2log y` whenever `log y>=1`,
the minimum length satisfies `D/2>=y/(32(log y)^4)`. A sharper explicit
bound is also available: the first two positive terms in
`log2=2 sum_(j>=0) 3^(-2j-1)/(2j+1)` give `log2>56/81>69/100`.
Thus for `u=log y>=20`,
`ell<100u/69+1<=3u/2`, and therefore
`D/2>=8y/(81u^4)>y/(11u^4)`. No derivative is transferred across an
integer jump: these are pointwise envelopes for every real `u>=20`.

This target optimization reduces a sufficient proof cost. It supplies no
lower bound on the mathematical problem and no new square cutoff by itself.
At cutoffs with `ell` in the hundreds of thousands or higher, the list and
radius inequalities are far below the exponential order `n`; the analytic
interface and controller remain the likely active constraints.

## Reproduction and preservation

Executable replay details are recorded in [Provenance](../PROVENANCE.md#optimized-bound).
The program checks the exact polynomial envelopes for integer exponents,
the small CRT lifting mechanism, grid coverage and reverse reconstruction,
and an actual exact-total list with independently trial-divided target
primes. It also retains explicit negative controls. These checks test finite
mechanisms and rational inequalities; they do not substitute for this proof,
the prime imports, the complete controller, or review of their composition.

[Manuscript index](../README.md) · [Optimized theorem](../optimized-bound.md) · [Source and review record](../PROVENANCE.md#optimized-bound)
