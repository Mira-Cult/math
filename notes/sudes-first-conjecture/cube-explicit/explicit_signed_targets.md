# Finite logarithmic-window targets for the full signed cube

Public proof manuscript. See [provenance](../PROVENANCE.md#explicit-prime-cube) for the pinned sources, internal review and verification limits.

## 1. Exact pool, quantities, and finite input contract

Let `n>=11` be odd and let


```math
A=\{p_2,\ldots,p_{n^3+1}\},\quad X=\max A,\quad
 T=\sum_{p\in A}p,\quad m=T/n^3,\quad \mu=T/n^2=nm.
```


The targets constructed here are primes that will be *line sums*. They need
not belong to `A`, and they may repeat. No target is added to the entry pool.
The later controller must permute exactly `A` once each.

Put


```math
L=\log X,\qquad e=\lceil\log_2(2nX)\rceil,\qquad
 d=\mu/(\rho L^b),                                             \qquad\text{(T1)}
```


where `b` is an integer at least two and `rho` is a positive rational.
The finite geometric/size assumptions
for this manuscript are


```math
\begin{split}
 &n^3\le X,\qquad X/4\le m\le X,\qquad L\ge2,\qquad \rho L^b\ge16,\\
 &n\ge54000e^{11},\qquad d\ge2^{20}e^{11}.                     \qquad\text{(T2)}
 \end{split}
```


The crude `X/4` lower mean bound is sufficient here; a sharper proved pool
mean may be used in the global composition. The upper bound `m<=X` is exact.
The lower bounds and all numerical domains in (T2) are obligations of that
composition, not assertions inferred from finite examples.

Let `g` be any even integer with


```math
2\le g\le16\lceil\log_2 X\rceil.                             \qquad\text{(T3)}
```


For every real center


```math
y\in[\mu-2d,\mu+2d],\qquad \ell_y=\lceil\log_2 y\rceil,       \qquad\text{(T4)}
```


assume the following two finite count hypotheses for every half-open real
interval `I` contained in `[y-d,y+d]` and of length at least `d/500`:


```math
\pi(I;g,a)\ge\frac{|I|}{4g\ell_y}
 \quad\text{for every reduced class }a\pmod g,                  \qquad\text{(T5)}
```



```math
\pi(I;q,a)\ge\frac{|I|}{4q\ell_y^9}
 \quad\text{for every }2\le q\le128\ell_y^2
 \text{ and every reduced class }a\pmod q.                     \qquad\text{(T6)}
```


These requests include the shifted finishing center and all subsequent face
centers. They are uniform over every allowed gap, residue prescription and
axis matrix produced below. They are not replaced by a count at `X` or at
one representative center.

The elementary bounds needed at every such center are


```math
\frac{\mu}{2}\le y\le2\mu\le2nX,\quad
 y\ge\frac{nX}{8}\ge X,\quad
 \lceil\log_2 X\rceil\le\ell_y\le e,\quad d\le y/4.            \qquad\text{(T7)}
```


Indeed `2d<=mu/8` follows from `rho L^b>=16`, so the first containment is
deliberately weaker than the actual one. Then `m>=X/4` and `n>=11` give
`y>=nX/8>=X`. Finally `d/y<=2/(rho L^b)<=1/8<1/4`. Thus the gap bound
has the literal `g<=16 ell_y` form required by the finite list lemma,
without an asymptotic comparison of logarithms.

## 2. The imported finite list lemma and its precise boundary

The only target-construction import is **FL**, the finite target-list lemma
in [finite target-list proof](../explicit-targets.md) at PR77 scientific revision
`f519b7fd796393cd6ab202f6790fe1824e6fc22f`. Its source bytes have SHA-256

`0e6ff5f0c26c6a2a6e66d0ae2b1a2ef581f282662a8e772e827ba04fd72f45e1`.

These bytes are identical to the same file at the cube's original import,
`c2118dfad1aeb660d66308dc6a94d6c959f5010c`. The later square cutoff is
not a premise of this manuscript. The standalone replay includes the
specified finite source and its elementary grid/binning source.

FL says: for `y>0`, `ell=ceil(log2 y)>=2`, even `2<=g<=16ell`,
and `k` requested unit classes `a_i mod g`, if


```math
ky\in\mathbb Z,\quad \sum_i a_i\equiv ky\pmod g,\quad
 k\ge54000\ell^{11},\quad 2^{20}\ell^{11}\le d\le y/4,         \qquad\text{(FL1)}
```


and the two count assumptions (T5),(T6) hold with that `y,ell,d`, there
are primes `t_i` with


```math
t_i\equiv a_i\pmod g,\qquad |t_i-y|\le d,\qquad
 \sum_i t_i=ky.                                               \qquad\text{(FL2)}
```


The proof uses repeated target values legitimately. A class appearing at
least `k/g` times supplies a repeated difference `h<=8g ell<=128ell^2`.
It fills an `h`-grid with at most `32ell^10` prefix slots and then
`100(P+1)` midpoint-controlled repeated pairs. At most `3332ell^10`
positions are reserved, while `k/g>=3375ell^10`; at least three free
positions remain. CRT lifts their prescribed original classes, including
overlapping prime powers. Greedy discrepancy in the remaining coordinates
is at most `d`, and the complete grid corrects the exact total. The two
elementary grid facts used there are C1 and C2 of the pinned
[complete-grid reservoir proof](../controller.md): touching/overlapping translated grids cover
their union, and bin extremes in one residue class give the stated
bounded difference. No ineffective asymptotic conclusion from that
older reservoir manuscript is imported.

Here every use has **`k=n`**, including the finishing use for the symmetric
matrix. It is incorrect to replace this by `k=n^2`: only the `n` diagonal
positions are available at that stage. Equations (T2),(T7) imply all the
length/radius/modulus conditions (FL1), with its original constants.
The relevant total and residue congruence are verified separately for
each invocation below.

## 3. Symmetric axis targets using exactly n finishing positions

Fix any symmetric matrix of unit classes `a_ij mod g` whose weighted total
over the `n^2` labeled positions is `T mod g`. For every non-diagonal
orbit `{(i,j),(j,i)}`, choose a prime in its prescribed class on either
side of `mu`, each within distance `d` of `mu`. Such primes exist by
(T5) in


```math
(\mu-d,\mu-d/2],\qquad (\mu+d/2,\mu+d].                       \qquad\text{(T8)}
```


Each has length `d/2`. Its lower count is at least
`d/(8g ell_mu)>=2^20 e^11/(128 e^2)>1`, by (T2),(T3),(T7).
In particular the lower and upper choices have the required strict signs.

Process these orbits in any fixed order, assigning the same selected prime
to both positions. Write


```math
E=\sum_{\text{completed }i\ne j}(P_{ij}-\mu).
```


Each orbit has weight **two**. If `E>=0`, use the lower choice; otherwise
use the upper choice. The next increment has the opposite sign and
magnitude at most `2d`, so induction gives


```math
|E|\le2d                                                      \qquad\text{(T9)}
```


after every orbit, irrespective of the number of orbits. There is no
probabilistic discrepancy bound and no loss proportional to `n^2`.

Let


```math
T'=T-\sum_{i\ne j}P_{ij}\in\mathbb Z,\qquad
 y'=T'/n=\mu-E/n.                                             \qquad\text{(T10)}
```


Exactly `n` diagonal positions remain. Their requested classes sum to
`T' mod g`, since every completed labeled entry has its prescribed class
and the original full matrix had total `T mod g`. Moreover


```math
|y'-\mu|\le2d/n\le2d/11\lt d/4.                                \qquad\text{(T11)}
```


Apply FL to those `n` positions at center `y'`, radius `d`, and exact
integer total `T'`. This center belongs to (T4), and (T2),(T7) verify
the literal conditions (FL1). The resulting matrix `P` is symmetric,
consists of primes in the requested classes, and satisfies


```math
\sum_{i,j}P_{ij}=T,\qquad
 |P_{ij}-\mu|\le(1+2/n)d\le\frac54d.                           \qquad\text{(T12)}
```


The non-diagonal entries have the stronger radius `d`. All primes exceed
two, because their intervals lie far above `X/2>=n^3/2>2`.

Use the same symmetric matrix as each directional axis-target array:


```math
U_0(j,k)=P_{jk},\quad U_1(i,k)=P_{ik},\quad U_2(i,j)=P_{ij}.     \qquad\text{(T13)}
```


The three directional grand totals are `T`. Every axis plane-marginal
identity follows by equality of row/column sums of the same symmetric
matrix. For example, `sum_j U_0(j,k)=sum_i U_1(i,k)` is equality
of two copies of the same column sum; the two other types use symmetry.
Thus (T13) verifies all axis identities, not merely their grand totals.

## 4. Six exact section totals and four independent body targets

Write `bar i=n-1-i`, and set


```math
S_+=\sum_i P_{ii},\qquad S_-=\sum_iP_{i,\bar i},\qquad
 y_+=S_+/n,\quad y_-=S_-/n.                                   \qquad\text{(T14)}
```


Both `S_+` and `S_-` are odd integers, being sums of `n` odd primes.
In fact `y_+=y'`; in either case the uniform bound (T12) gives


```math
|y_\pm-\mu|\le(1+2/n)d\le\frac54d.                           \qquad\text{(T15)}
```


For each pair of varying coordinates and each sign, the desired face
family has `n` members and exact family total `S_+` or `S_-` as
appropriate. After `P` is fixed, choose any list of `n` units modulo
`g` summing to that family's odd total modulo `g`. Apply FL to that
list at `y_+` or `y_-`, radius `d`, length `n`, and exact total
`S_+` or `S_-`. The center is in (T4), so all six applications have
their actual hypotheses checked. Each family sum equals its required
diagonal-square aggregate of axis targets **as an integer**.

If `F` is any resulting face target, then


```math
|F-\mu|\le(2+2/n)d\le\frac{24}{11}d\lt \frac94d.                \qquad\text{(T16)}
```


The section totals themselves may be composite and may be nonunits
modulo `g`. FL requires the individual residues to be units and their
sum to have the correct residue; it does not require the total to be
a unit or a prime. Target values can coincide between or within
families without affecting any step.

For each of the four body lines, prescribe any unit class modulo `g`
and choose a prime in that class within `d` of `mu`, using (T5).
There is no body-total requirement. The proved full integer-image
theorem in [signed_incidence.md](../cube/signed_incidence.md), valid for odd
`n>=11`, supplies the exact compatibility boundary: the axis equations
and the six face-family total equations are the entire list; no
additional body relation is imposed. This finite target construction
does not extrapolate an integer-image statement from rational rank.

Consequently every required signed line has a prime target, all targets
are units modulo `g`, all compatibility equations hold exactly, and


```math
\max_{\lambda}|t_\lambda-\mu|\le(2+2/n)d\le\frac{24}{11}d\lt 3d. \qquad\text{(T17)}
```


This proves the following finite statement.

**Theorem LST (logarithmic signed targets).** Under (T1)--(T6), every
admissible symmetric axis residue pattern, every set of six admissible
face residue lists selected after that axis matrix, and every four unit
body residues are simultaneously realized by compatible prime targets
with radius `3mu/(rho L^b)` and the sharper bound (T17).
Repetition is allowed. In particular some such
compatible prime target vector exists for every allowed `g`.

### Why admissible residue patterns always exist

For any even `g` and odd residue `S mod g`, three units sum to `S`.
At every odd prime power `p^v||g`, set the first summand to `1`,
choose the second modulo `p` different from `0` and `S-1`, and
set the third equal to `S-1` minus the second modulo `p^v`.
At most two classes are excluded, including when `p=3`; choose any
lift of the second. The third is then a unit. At the power of two,
choose the first and second odd, so the third is odd because `S`
is odd. CRT combines these choices into three global units.

For a length-`n` list with odd total, put `n-3` ones first and use
the construction for the remaining odd residue. For the symmetric
axis matrix, put ones in every labeled position except three
diagonal positions and use the same construction there. Since
`n^2-3` is even and `T` is odd, the residual is odd. Thus neither
the axis nor face step hides a residue-existence hypothesis. The
argument includes `g=2`, when every chosen unit is `1` and no
modular repair is needed by the physical controller.

## 5. Conversion from a uniform effective interval theorem

The following implication isolates exactly what the replacement analytic
proof must furnish. Let `kappa>0` be a fixed rational window denominator
and let `s>=b` be an integer. Suppose the analytic theorem proves,
for every center `Y` with `u=log Y>=U`, every interval `I` in
`[Y/2,2Y]` of length `H>=Y/(kappa u^s)`, and every indicated reduced class,


```math
\begin{array}{ll}
 \pi(I;q,a)\ge H/[2\varphi(q)\log(2Y)],&2\le q\le64u,\\
 \pi(I;q,a)\ge H/[4q\lceil\log_2Y\rceil^9],&2\le q\le512u^2.
 \end{array}                                                  \qquad\text{(A)}
```


The analytic source must include endpoint conventions, all moduli including
odd ones, primitive-conductor normalization, and any exceptional-zero
contribution. This manuscript neither deletes an exceptional term nor
assumes it has favorable sign. The two lines of (A) are separate promises:
the weak density is not substituted into the first close-pair step of FL.

In addition to (T2), suppose


```math
\log(7\mu/8)\ge U,\qquad
 \kappa L^{s-b}\ge500\rho+\frac{1000}{L^b}.                    \qquad\text{(T18)}
```


For any center (T4), let `u=log y`. The actual lower bound from
`rho L^b>=16` is `y>=7mu/8`, so the stated analytic domain applies.
By (T7), `u>=L>=2`, `y<=mu+2d`, and the relevant windows lie
inside `[y/2,2y]`.
For their shortest interval,


```math
H\ge\frac d{500}=\frac{\mu}{500\rho L^b}
 \ge\frac{\mu(1+2/(\rho L^b))}{\kappa L^s}
 \ge\frac y{\kappa u^s}.                                     \qquad\text{(T19)}
```


Using `log 2>2/3` and `u>=2`, one has


```math
\ell_y\le\frac32u+1\le2u,
 \qquad128\ell_y^2\le512u^2,
 \qquad g\le32L\le32u\lt 64u.                                   \qquad\text{(T20)}
```


Therefore (A)'s weak estimate is exactly (T6). Its strong estimate
implies (T5), since `phi(g)<=g` and
`log(2y)=u+log2<=2ell_y`: indeed `u<=ell_y log2` and
`ell_y>=1` give `u+log2<2ell_y`. Every prime request is thus
within the source's actual modulus, length, center and endpoint domain.

In the same-exponent case `s=b`, the length comparison is exactly


```math
(\kappa-500\rho)L^b\ge1000.                                 \qquad\text{(T18a)}
```


For example, `rho=2,kappa=1001` requires only `L^b>=1000` and
uses the source window `Y/(1001 u^b)`. No exponent gap is needed.
The earlier exploratory choice `rho=1,b=37,s=40,kappa=1` also satisfies
(T18) when `L^3>=1000`; it is retained as a separate sufficient
profile rather than substituted into the optimized one. The exact
center shift is responsible for the positive extra term in (T18a);
using `kappa=500rho` would omit it.

## 6. Controller radius, explicit order envelopes, and persistence

For an integer `a_0>=0`, let `K_0=ceil(n/L^a_0)`. If an explicit
pool estimate gives `m<=MX` with `0<M<=1`, then, for any fixed
`N>=11` such that `n>=N`, the sharp bound is


```math
\frac{\max_\lambda|t_\lambda-\mu|}{K_0X}
 \le\frac{(2+2/n)M}{\rho L^{b-a_0}}
 \le\frac{(2+2/N)M}{\rho L^{b-a_0}}.                          \qquad\text{(T21a)}
```


The convenient coarser version is


```math
\frac{3d}{K_0X}\le\frac{3M}{\rho L^{b-a_0}}.                  \qquad\text{(T21)}
```


For any allocated fraction `B>0` of the controller box, the sufficient
condition is `3M<=B rho L^(b-a_0)`. With `b=a_0`, `rho=2`,
`M=3/5`, and `B=1`, every target is within `9K_0X/10` of `mu`.
There is no need to shrink to one hundredth of the box when the finite
controller realizes the full box. The earlier conservative profile
`a_0=35,b=37,rho=1,M=1,B=1/100` is separately paid by `L^2>=300`.
The sharper coefficient `24/11` may replace `3` if that interface is
chosen explicitly. All these are pointwise inequalities for the actual
ceiling; jumps in `K_0` cause no loss.

The refined profile `a_0=b=16`, `rho=101/100`, `N=200`, and
`M=501/1000` has the exact target/controller ratio bound


```math
\frac{(201/100)(501/1000)}{101/100}
 =\frac{100701}{101000}\lt 1.                                   \qquad\text{(T21b)}
```


Its analytic interval denominator is `kappa=506`, because
`506-500(101/100)=1`; the exact finite window condition is
`L^16>=1000`. This is a target-interface improvement conditional on
the separately proved sharper pool mean and full controller box.
It does not declare that the complete numerical cutoff has decreased.

Here is a convenient all-tail evaluation of the algebraic conditions,
separate from the analytic domain `U`. Assume the global prime estimates
have established `n^3<=X<=n^4` and `m>=X/4`, and put
`v=log2 n`. For every real `v>=2`,


```math
2v\le L\le4v,\quad e\le6v,\quad
 \mu\ge n^4/4,\quad
 d\ge\frac{2^{4v}}{4\rho(4v)^b}.                              \qquad\text{(T22)}
```


The logarithm bounds use `2/3<log2<1`. The ceiling bound is
`e<=1+5v+1<=6v`; it applies at every integer order, including
every jump of `e`.

Consequently the target size conditions follow from


```math
2^v\ge54000(6v)^{11},\qquad
 2^{4v}\ge2^{22}\rho(4v)^b(6v)^{11}.                          \qquad\text{(T23)}
```


For the historical `b=37,rho=1`, the first `b=16,rho=2` profile,
and the refined `b=16,rho=101/100` profile, both inequalities hold
at **`v=121`**, by exact
integer/rational comparison, and persist for all real `v>=121`.
The logarithmic
derivatives of their left/right ratios are respectively


```math
\log2-11/v\gt 2/3-11/v\gt 0,\qquad
 4\log2-(b+11)/v\gt 8/3-(b+11)/v\gt 0.                              \qquad\text{(T24)}
```


All remaining conditions in (T2) are increasing powers of the unrounded
lower bound `2v`. For `s>=b` the difference between the two sides of
(T18) increases with `L`; for `b>=a_0` the denominator in (T21)
is nondecreasing. Hence their endpoint comparisons also persist.
The exact checker retains every comparison, rather than treating a
sample of larger orders as a persistence proof. For each of these displayed
profiles, the sufficient algebra-only floor is therefore `2^121` on the order,
subject to the displayed global pool bounds. It is **not a cube cutoff**:
the analytic domain, physical packing, centering and correction bounds
must also hold. The analytic target domain can use the actual `7mu/8`
lower center. One convenient (nonoptimal) elementary envelope is


```math
\log(7\mu/8)\ge(4v-3)\log2,                                \qquad\text{(T25)}
```


instead of demanding the same logarithmic floor at `X`. If the separate
pool estimate gives `m>=12X/25`, the better literal bound is


```math
\log(7\mu/8)\ge\log X+\log n+\log(21/50).                   \qquad\text{(T25a)}
```


The global composition may use (T25a) directly; it need not pay the
weaker elementary envelope (T25).

The executable check in `code/verify_explicit_signed_targets.py` uses
only integer and rational arithmetic. It reports the first sufficient
integer `v` for its separate envelopes, verifies the declared floor,
and checks the derivative signs that establish the complete real tail.
It does not implement a prime-count oracle or construct a cube at
the numerical cutoff.

## 7. Dependency and verification boundary

The exact-total target argument has these distinct inputs:

| Input | Kind | Used for |
|---|---|---|
| Exact odd-prime pool total `T`, (T2)'s mean and size bounds | Finite quantities plus separately proved explicit estimates | Actual center, integer totals, local domains |
| FL at the specified raw source hash | Finite imported lemma | `n` diagonal finishing slots and six length-`n` face lists |
| C1/C2 from the pinned reservoir source | Elementary finite lemmas inside FL | Complete grid and repeatable difference growth |
| Uniform effective interval theorem (A) with (T18) | Analytic import/derivation, separately reviewed | Both literal FL count hypotheses after all center shifts |
| Signed integer-image theorem for odd `n>=11` | Finite exact theorem | Completeness of axis plus six face identities; no body relation |
| Physical signed-cube controller | Separate finite theorem | Converts these targets into one exact-pool permutation |

The old Thorner--Zaman short-window consequence is not used in this new
composition. All windows here have an inverse-logarithmic radius, and
(T19) checks the length comparison that a long-interval error requires.
The old theorem remains an independent fallback.

Retained target and physical fixtures are checked before changing any
interface. Their prime lists, exact-pool arrays, integer-image certificates
and physical swaps have distinct scopes. Their successful replay and
mutation rejection do not establish (A), the new physical controller, or
an unconditional numerical theorem. Those conclusions require the
mathematical proofs and the final composition review.
