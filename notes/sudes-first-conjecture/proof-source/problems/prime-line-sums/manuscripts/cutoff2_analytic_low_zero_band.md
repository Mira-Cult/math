# Smaller-order progression supplies from the signed low-zero sum

Author: `/root/analytic_redesign`, following `/root`'s identification of
the discarded boundary term. This additive source changes no frozen Q30,
AB, SM, SE, GD, SO or SQ file. All labels below are manuscript-local.
The argument requires independent nonauthor review at its exact scientific
revision. The executable certificate establishes finite inequalities and
source bindings, not the analytic imports or a complete square theorem.

The boundary cancellation used here is already explicit in the proof of
BMOR Lemma 2.11. The improvement specializes that argument to the small
conductors actually requested; it does not assume new zero computations
or an unproved zero hypothesis.

Counting intervals are half-open `(b,c]` unless a seed interval is
explicitly closed. The lower counts also hold for the corresponding
closed intervals.
All unmarked logarithms are natural; the integer e in LZ4 is explicitly
defined using a base-two ceiling.

## LZ1. Source conventions and the signed partial summation

The primary source is Bennett--Martin--O'Bryant--Rechnitzer,
*Explicit bounds for primes in arithmetic progressions*, Illinois J. Math.
62 (2018), 427--532,
[original author-hosted PDF](https://personal.math.ubc.ca/~gerg/papers/downloads/EBPAP.pdf)
and the [inspected author mirror](https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf).
The following conventions and domains were checked in the original source:

| Locator | Exact use |
|---|---|
| (2.2), p.438 | `Z(chi)` is the critical-strip multiset; its elements retain multiplicity, and `Z(chi)=Z(chi*)` for an induced character |
| Proposition 2.1, pp.438--439 | The smoothed formula for the prime-power sum; its `W_q` pays the primitive/imprimitive correction |
| Definition 2.2, p.440 | `N(T,chi)` counts `abs(gamma)<=T`, both signs, with multiplicity |
| Proposition 2.5, p.441 | For every `T>=1`, the two-sided count has actual primitive conductor `d`, with `C_1=.399,C_2=5.338` |
| Proposition 2.7, p.441 | Verified critical-line zeros through `10^8/d` for `1<d<=100000`; conductor one through `30610046000` |
| Lemma 2.11 and its proof, pp.442--443 | The partial-summation boundary is `N(H)/H-N(H_0)/H_0` |
| Proposition 4.34, pp.478--479 | The unchanged higher-zero region with constant `R=5.6` |

Let a character have primitive conductor `d<=Q`, and suppose its zeros
through height `H>=1` have real part `1/2`. Write `N(t)=N(t,chi)`.
The zeros with `abs(gamma)<=1` each contribute at most 2 to
`1/abs(rho)`. For the remaining zeros, `1/abs(rho)<=1/abs(gamma)`.
The closed-height convention gives the exact identity

\[
 \sum_{1<|\gamma|\le H}\frac1{|\gamma|}
    =\frac{N(H)}H-N(1)+\int_1^H\frac{N(t)}{t^2}\,dt.
                                                               \tag{LZ1}
\]

Consequently

\[
 \sum_{|\gamma|\le H}\frac1{|\rho|}
 \le N(1)+\frac{N(H)}H+\int_1^H\frac{N(t)}{t^2}\,dt.           \tag{LZ2}
\]

This combines `2N(1)-N(1)` before any upper bound for `N` is inserted.
It does not bound a negative count term in the wrong direction. It also
does not add another factor for negative ordinates: those ordinates are
already included in `N`. Zeros exactly at heights 1 or H and repeated
zeros satisfy the same Stieltjes identity. A possible zero at height 0
is in `N(1)` and has `abs(rho)=1/2`; no division by that ordinate occurs.

Proposition 2.5 gives, with the actual conductor retained,

\[
 N(t)<\frac t\pi\log\frac{dt}{2\pi\mathrm e}
                       +C_1\log(dt)+C_2\qquad(t\ge1).
\]

The right side increases with `log d`, its coefficient being
`t/pi+C_1>0`. We may therefore replace `d` by `Q` in this **one-sided
upper majorant**, after (LZ2) has made all count coefficients nonnegative.
No two-sided zero-count theorem with conductor `Q` is asserted.

Put

\[
 \nu=\log Q,\qquad \lambda=\log(QH),\qquad
 c=\log(2\pi)+1.
\]

Integrating the majorant in (LZ2) gives

\[
 \boxed{\displaystyle
 \mathcal K(Q,H)=
 \frac{(\nu-c)+(\lambda-c)
       +\tfrac12\{(\lambda-c)^2-(\nu-c)^2\}}{\pi}
       +2C_1\nu+C_1+2C_2-\frac{C_1}{H}.}
                                                               \tag{LZ3}
\]

In detail, the counting-error integral is

`C_1(nu+1)+C_2-[C_1(lambda+1)+C_2]/H`.

Adding the error terms from `N(1)` and `N(H)/H` leaves
`2C_1nu+C_1+2C_2-C_1/H`. This verifies the sign of the last term
in (LZ3). The reciprocal-zero sum in (LZ2) is bounded by `K(Q,H)`.

## LZ2. Exact reciprocal-zero caps

The directed rational certificate proves the following inequalities:

| Application | `Q` | `H` | Upward enclosure of `K(Q,H)` | Adopted rational cap `K_0` |
|---|---:|---:|---:|---:|
| Entry and prefix supplies | 30 | `10^8/30` | 57.524725046606696 | `2301/40=57.525` |
| Bounded target classes | 44 | `10^8/44` | 57.860243189674102 | `57861/1000=57.861` |
| Fixed parity seed | 2 | `30000000000` | 94.098851739010097 | `941/10=94.1` |

For the first two rows, every actual primitive conductor is at most Q,
so the chosen H is within its published verification range. For the last
row there is only one character modulo 2, and its primitive conductor is
1. The height is below the published zeta verification height. The value
Q=2 is used only as a one-sided upper bound for that conductor in (LZ3);
it does not posit a new height theorem for another character.

The arithmetic uses rational intervals throughout (LZ3), including its
subtracted square. A sixteen-term alternating arctangent calculation and
the identity `pi=4 arctan(1/2)+4 arctan(1/3)` enclose pi; directed
logarithm bounds then enclose nu, lambda and c. Intervals that cross zero
are squared with lower endpoint zero. Thus negative `nu-c`, which occurs
in the parity row, is handled explicitly rather than by an invalid
monotonic substitution in its square.

## LZ3. Entry supplies below order `2^19`

Retain the prescribed pool and notation

\[
 X=p_{n^2+1},\quad T=\sum_{j=2}^{n^2+1}p_j,\quad
 m=T/n^2,\quad y=T/n,\quad E=\lceil\log_2 X\rceil.
\]

Every statement in this section assumes an **actual even modulus
`2<=q<=30`**. The selected-gap assertion remains a separate controller
obligation; this section places no upper bound of 30 on E. The complete
totient table proves `phi(q)<=12`, attaining 12 at q=26 and q=28.

Use the pointwise argument of [Q30, section 3](cutoff2_analytic_quality_band.md),
now with `K_0=57.525` in place of 110, and with

`Q=30`, `Phi=12`, `r=16`, `tau=15/10^7`.

In Q30's definitions of `S_z`, `A_r`, `a_0` and `Gamma`, keep the
high-zero sum unchanged and replace only

\[
              \Gamma=\Phi\{K_0(1+r\tau/2)+2\}.                \tag{LZ4}
\]

The source proposition then gives, whenever `log x>=z`,

\[
 \varphi(q)\left|\theta(x;q,a)-\frac{x}{\varphi(q)}\right|
        \le a_0x+\Gamma\sqrt x+\Phi(25\log x+62).              \tag{LZ5}
\]

The original primitive-character correction remains paid in `W_q`.
Proper prime powers are removed by the frozen SM estimate
`psi-theta<2sqrt(x)` for `log x>=24`, rederived there from
Rosser--Schoenfeld Theorem 4, p.70 of the
[original scan](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf).
No new substitution between primitive and imprimitive prime-power sums
is made. The bound (LZ3) does not change which zeros are included.

Let `c_-=79/700`, `c_+=621/700`, and require the centers to satisfy
`c_-X<=Y<=c_+X`. This covers the controller's centers if the separate
mean bound `.47X<m<.53X` and extent `w=3/28` hold. For each row below,
the following conclusions hold for **every larger order** than the
listed threshold:

| Lower order condition | `U<log X` | `z` | Practical `(A,N)` | Largest certified entry denominator `A_*` | Largest certified bridge denominator `W_*` |
|---|---:|---:|---:|---:|---:|
| `n>=2^18` | 28.170304 | 25 | `(924,99)` | 952 | 518 |
| `n^4>=2^73` | 28.530671 | 26 | `(1120,120)` | 1135 | 618 |
| `n^2>=2^37` | 28.890850 | 26 | `(1344,144)` | 1352 | 737 |

The fractional logarithmic thresholds are `v=73/4` and `v=37/2`,
where `v=log_2 n`. Their displayed integer-power conditions avoid any
unstated rounding of those thresholds. In every practical profile,
`N/A=3/28`; the last row also permits the wider half-width from
`(A,N)=(1316,141)`.

For every `1/A_*<=delta<=1/100`, each centered entry interval
`(Y-delta X,Y+delta X]` contains at least

\[
                         \frac{\delta X}{\varphi(q)\log X}.
                                                               \tag{LZ6}
\]

Every interval inside `[X/4,3X/4]` of length `H>=X/W_*` contains
at least `H/[2phi(q)log X]` class primes. In particular, all three
profiles support the requested prefix width `X/512`. Also the wider
global pool `(X/8,X]` contains at least

\[
                         \frac{693X}{800\varphi(q)\log X}.
                                                               \tag{LZ7}
\]

### Domains and whole-tail proof

Rosser--Schoenfeld Theorem 3 corollary (3.12), p.69, gives

`log X>2v log2+log(2v log2)`.

The exact certificate evaluates this increasing lower envelope at each
listed rational v. Paying the largest permitted half-width gives the
smallest bin endpoint `(18/175)X`. Its logarithm is greater than
25.895889783972, 26.256256783972 and 26.616435783972 in the respective
rows. Thus the actual endpoints exceed the chosen z, not merely their
centers. All endpoints are below `(157/175)X<X`. The bridge and global
lower endpoints are larger still.

For all rows, `z>=25>24`, `H=10^8/30>=1000`, `r tau<1/100`,
`exp(z)>3`, and the high-zero tangent-integral parameter
`r-z/[R(log10^8)^2]` is positive. These explicitly verify the original
smoothing, verified-height, high-zero and prime-power domains.

With `u=log X`, apply (LZ5) to the endpoints as in Q30. The three
normalized errors are

\[
\begin{split}
 B(u)&=2c_+a_0+2\Gamma\sqrt{c_+}\,e^{-u/2}
                     +2\Phi(25u+62)e^{-u},\\
 B_b(u)&=\tfrac32a_0+2\Gamma\sqrt{3/4}\,e^{-u/2}
                     +2\Phi(25u+62)e^{-u},\\
 G(u)&=\tfrac98a_0+(1+\sqrt{1/8})\Gamma e^{-u/2}
                     +2\Phi(25u+62)e^{-u}.
\end{split}                                                     \tag{LZ8}
\]

The certificate proves `A_*B(U)<1`, `2W_*B_b(U)<1`, and
`G(U)<7/800`. It also checks the practical A and width 512 ratios:

| Lower `v` | Practical entry ratio, upper | Width-512 bridge ratio, upper | Global one-percent loss ratio, upper |
|---:|---:|---:|---:|
| 18 | 0.970372319 | 0.987067507 | 0.086021683 |
| 18.25 | 0.986431972 | 0.827532051 | 0.072107259 |
| 18.5 | 0.993640628 | 0.694374316 | 0.060493435 |

Subtracting these errors from the theta main terms and dividing by
`log X` gives (LZ6)--(LZ7) and the bridge count. The high-zero majorant
at fixed z remains valid because `x^(beta-1)` decreases with x.
Every nonconstant term in (LZ8) decreases for `u>=U>1`, while a_0
stays fixed. Hence the same inequalities hold at every larger order.
This proof uses fixed q<=30 and valid smooth envelopes, independent of
all ceiling jumps in E and all changes in the actual selected gap.

The maximal integers in the table describe the particular rational
majorants: the verifier checks their strict inequalities and the reverse
comparisons at the next integers. They are not lower bounds on prime
supply or on the square problem.

## LZ4. Target supplies for `2^18<=n<=2^19`

Assume the separately supplied mean bounds `.47X<m<.53X`, and set

\[
 e=\lceil\log_2 y\rceil,\qquad
 L=\lceil(693148/10^6)(e+1)\rceil,\qquad D=y/R_0.
\]

For every real `4<=R_0<=5000`, the two dense-target supply premises hold:

1. `[y-D/4,y+D/4]` contains at least
   `(99/100)(D/2)/log(2y)` odd primes.
2. For every even `2<=q<=(50/49)L`, each reduced class, and every
   half-open interval in `[y-D,y+D]` of length at least `D/2`, the count is at
   least its length divided by `2phi(q)log(2y)`.

The exact-total target lemma's finite grid, list length and parity
conditions remain separate obligations. Its permissible repetition of
target prime values is unchanged.

### Actual modulus and endpoint bounds

For `n<=2^19`, put `j=n^2+1<=2^38+1`. The imported
Rosser--Schoenfeld corollary (3.13), valid for j>=6, gives

`p_j<j(log j+log log j)`.

Since `log j<39log2<28` and `log log j<log28<4`,

\[
 X<32(2^{38}+1)<2^{44},\quad y<2^{63},\quad e\le63,\quad L\le45.
                                                               \tag{LZ9}
\]

Every requested even target modulus is therefore at most 44:
`(50/49)L<=2250/49<46`. The complete totient table through 44 proves
`phi(q)<=20` for all those even moduli.

At the lower order, the lower index and mean bounds give

\[
 \log y>28.170304+18\log2+\log(.47)>39.891930665800.
\]

Every target endpoint has logarithm greater than
`28.170304+18log2+log(.47)+log(3/4)>39.604248593349>39`.
The seed endpoints are in this same region. These comparisons hold for
every R_0>=4, without assuming a narrow interval before checking its domain.

### Progression and parity-seed errors

Use `Q=44`, `Phi=20`, `z=39`, `r=16`, `tau=22/10^7`, and the
second low-zero cap `K_0=57.861`. The same primitive-correct formula
gives relative theta error less than

\[
                  0.000022752411458<\frac1{8(5000+1)}.          \tag{LZ10}
\]

The interval endpoints sum to at most `2y(1+1/R_0)`, and its length
is at least `y/(2R_0)`. Thus the theta error removes less than half
the main term. Dividing by `log(2y)` proves the second supply premise.
All original domains hold: H=10^8/44 exceeds 1000, z exceeds 24,
the smoothing width is admissible, and the high-zero tangent parameter
is positive.

For the parity seed, use its unique conductor-one character, height
`H=30000000000`, order `r=20`, width `tau=202/10^12` and z=39.
The reciprocal low-zero sum is at most 94.1 by the third row of LZ2.
For higher zeros simply use `x^(beta-1)<=1`. The unchanged SM
integration-by-parts majorant gives

\[
 S\le H^{-20}\left\{\frac{25/20+1/20^2}{\pi}
                          +\frac{2(25C_1+C_2)}H\right\},
\]

using `log(2H)<25`. The resulting relative theta error is less than

\[
                  0.000000328687258<\frac1{400\cdot5000}.       \tag{LZ11}
\]

The seed endpoints sum to `2y`, so their error loses less than one
percent of the main term `D/2`. This proves the first supply premise.
The actual height lies below the published zeta verification height;
the primitive correction, smoothing domain and prime-power removal are
paid as before. No new zero table is consulted.

The target error ratios at R_0=5000 are less than 0.910278478 and
0.657374516 respectively. All endpoint-dependent terms decrease as y
increases within the finite order band. The cap 44 is justified by
(LZ9) only on that band and is not extended beyond it.

At `n=2^19` the new target band overlaps the frozen AB target band.
A complete construction can change to its previously reviewed profile
there. AB retains its own R_0<=4400 range; this source does not extend
R_0=5000 to all larger orders. The fixed-q30 entry statements in LZ3,
in contrast, have the whole-tail ranges explicitly proved above.

## LZ5. Experiment outcome, recovery and verification scope

The tested hypothesis was that retaining the existing signed boundary and
the actual small-conductor logarithms could remove the dominant reciprocal
low-zero padding. The resulting cap 57.525 replaces 110 for entries,
and the complete exact comparisons now support the listed order-18,
order-18.25 and order-18.5 analytic profiles. The finite target modulus
bound and parity refinement together support R_0=5000 below order2^19.
Whether a full square construction can use these improvements remains
a coupled controller/composition question.

Run

```sh
python3 -B problems/prime-line-sums/code/cutoff2_analytic_low_zero_band.py
```

The complete manifest binds all transitive sources, rational parameters,
totient tables and analytic import locators. The verifier rejects missing,
empty, malformed, extra, duplicate or mismatched bindings and tests
physical source substitutions. It uses only exact integers and fractions,
with outward rational bounds for every transcendental quantity.

Boundary fixtures exercise repeated heights, both closed endpoints and a
central zero; they test the partial-summation bookkeeping without claiming
to certify the universal analytic identity. Numerical negative controls
reject insufficient low-zero caps, the next excluded entry/bridge
denominators, an invalid endpoint-log floor, and target R_0=5600 under
the stated sufficient bound. Frozen Q30 and its dependencies are replayed.
Imported zero verification, the handwritten calculus and the complete
construction remain matters for ordinary mathematical review, not formal
proof-kernel claims.
