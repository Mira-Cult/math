# Linear target windows and the actual entry modulus

This additive manuscript preserves the frozen
[cubic analytic refinement](cutoff_analytic_refinement.md) and
[quadratic-window corollary](cutoff_quadratic_window_analytic.md). Its
[exact rational certificate](../PROVENANCE.md#optimized-bound)
binds the complete five-file analytic dependency set. The two statements
below concern prime supplies. A controller that can use the larger target
radius, the small seed modulus, and the order-to-scale conversion are
separate obligations; this note alone asserts no square theorem.

The imported theorems and primary-source page locators are exactly those
recorded in [the first optimization](cutoff_analytic_optimization.md).
In particular, the proof uses the corrected primitive-character E2
derivation in [effective_pair_supply.md](../classical-primes.md), with
`psi(t,chi)=psi(t,chi*)-J_chi(t)` and its explicit omitted-prime-power
allowance. It retains the signed exceptional term. It neither assumes a
zero-free exceptional region nor treats the arithmetic certificate as a
proof of BMOR, MCC84, or that normalization.

Throughout this note, `log` is natural. Put


```math
u=\log Y,\quad \ell=\lceil\log_2Y\rceil,\quad
 F=\ell\bigl(7+2\lceil\log_2\ell\rceil\bigr)^2.
```


## 1. The two supply statements

**AT1 (linear target radius).** If


```math
\boxed{\log Y\ge13597},\qquad D=Y/\ell,
```


then every even `2<=q<=(369/1000)ell^2`, every reduced residue class
modulo `q`, and every real half-open interval `(b,c]` inside
`[Y-D,Y+D]`, of length `H>=D/2`, have prime count at least


```math
\boxed{H/(qF)}.                                           \qquad\text{(AT1a)}
```


For the same scale and interval, every even `q<=32ell` has the stronger
count


```math
\boxed{H/[2\varphi(q)\log(2Y)]}.                         \qquad\text{(AT1b)}
```


**AS-small (actual entry modulus).** If


```math
\boxed{\log Y\ge9000},\qquad 2\le q\le\ell,\quad q\text{ even},
```


then every reduced residue class modulo `q` and every real half-open
interval `(b,c]` inside `[Y/2,2Y]`, of length `H>=Y/50000`, have count
at least


```math
\boxed{H/[2\varphi(q)\log(2Y)]}.                         \qquad\text{(ASs)}
```


Both conclusions apply on the entire real scale tail. The half-open
convention is literal: the proof subtracts `theta(c)-theta(b)`. Thus
adjacent bins may partition an entry reservoir without sharing endpoint
primes or incurring an unrecorded boundary charge.

## 2. Common source and rounding envelopes

Use the already proved sharper normalized error (AL3): for even
`Q>=100000`, `log x>=4R_1(log Q)^2`,


```math
|\theta(x;Q,a)-M_{Q,a}(x)|\le
 \frac{253}{250}xv e^{-v}
 +\frac{4Qx e^{-v}}{\varphi(Q)}
 +2\log Q\log x+Q\log Q+2\sqrt x,
 \quad v=\sqrt{\log x/R_1}.                             \qquad\text{(AT2)}
```


Here `R_1=9.645908801`. The factor `4/phi(Q)`, spectral coefficient
`253/250`, exceptional sign, primitive-character correction, and all
source domains are precisely those of AL3. No domain relaxation is made.
Small even `q` is multiplied by a power of two until
`100000<=Q<200000`; other moduli are unchanged. Reduced classes partition
exactly through this lift in the present intervals, whose primes exceed
2. Multiplication of the summed error by `phi(q)` introduces `phi(Q)`,
which is at most `Q/2`.

Set


```math
a=1443/1000,\quad \alpha=3219/10000,\quad
 c_s=253/250,\quad c_y=2001/1000.
```


The certificate proves `6931/10000<log 2<7/10`. At all the stated
scales, pointwise including every ceiling jump,


```math
10u/7\lt \ell\le au,\qquad \log(2Y)\le\ell.
```


For an endpoint in `[Y/2,2Y]`, `log x>u-1` and `log x<u+1<2u`.
The exact inequality `R_1 alpha^2<1-1/U` at each base gives
`v>=alpha sqrt u`. Since `v exp(-v)` decreases for `v>1`, replacing
`v` by this lower bound majorizes the spectral error. The slightly smaller
`alpha` than in AL is intentional: the old envelope required an unnecessary
base above 16000 even when the original source domain was already valid.

The previous harmless remainder envelope remains available whenever
`Q<=288u^2` and `log Q<=u`: after multiplying the two endpoint errors
by `phi(Q)` and dividing by `Y`, the nonspectral part is at most


```math
r(u)=85000u^5e^{-u}+864u^2e^{-u/2}.                     \qquad\text{(AT3)}
```


All these inequalities are checked for each profile below.

## 3. Proof of the linear target supply

Fix `U=13597`, `C=369/1000`, and put


```math
B=\log(C\ell^2),\qquad
 L(u)=\log(Ca^2)+2\log u.
```


Then `Q<=C ell^2<=Ca^2u^2`, including the small-modulus lifts, and
`log Q<=B<=L(u)`. The actual endpoints satisfy
`b+c<=2Y(1+ell^{-1})<=c_yY`. The exact source-domain check is


```math
U-1\gt 4R_1 L(U)^2,                                     \qquad\text{(AT4)}
```


with a certified positive margin exceeding `0.026822851114`.
The ratio `(u-1)/L(u)^2` increases once `L(u)>4`, so AT4 covers every
larger scale and every permitted endpoint.

To retain enough of the exceptional main derivative, define `s_C` and
`B_0` by outward rational bounds
`s_C>=sqrt C`, `B_0<=log(C(10U/7)^2)`, as in AL7. Put


```math
z_0=\frac{40(1-1/U)}{a s_C},\qquad
 A=10^{-6}\left\lfloor10^6\left(z_0-\frac{z_0^2}{2B_0^2}\right)\right\rfloor
   =\frac{10667281}{250000}.                            \qquad\text{(AT5)}
```


BMOR Proposition 1.11 and `1-exp(-z)>=z-z^2/2` give on the whole
interval


```math
M'_{Q,a}(t)\ge\frac{A}{\varphi(Q)B^2}.                \qquad\text{(AT6)}
```


This argument covers the unfavorable exceptional sign; the other sign
and absence of an exceptional zero dominate it because `A<B_0^2`.
The lifted normalized exponential error divided by `Y` is at most


```math
f(u)=c_yCa^2u^2\left(\frac{c_s\alpha\sqrt u}{2}+4\right)
                     e^{-\alpha\sqrt u}.              \qquad\text{(AT7)}
```


The exact certificate proves


```math
\frac{2auL(u)^2}{A-1/2}\,[f(u)+r(u)]
 \lt 0.107045145685\lt 1\quad\hbox{at }u=U.                  \qquad\text{(AT8)}
```


For the exponential summand, its logarithmic derivative multiplied by
`u` is bounded above by
`7/2+4/L(u)-alpha sqrt(u)/2`, which is negative already at `U` and
decreases thereafter. The other summands decrease when
`u>6+4/L(u)` and `u/2>3+4/L(u)`, respectively. These base comparisons
are checked exactly. Thus AT8 holds on the full tail, without
differentiating a ceiling or changing integer modulus.

As `H>=Y/(2ell)`, AT8 spends at most
`(A-1/2)H/[phi(q)B^2]`. After subtracting this error from AT6, at
least `H/[2phi(q)B^2]` remains in theta weight. With
`j=ceil(log_2ell)`, use `B<=log2*(7+2j)`, `log(2Y)<=ell`, and
`2phi(q)<=q`. This gives AT1a with the stated integer `F`.

For AT1b, the frozen AS-macro proof already gives main derivative greater
than `3/[4phi(Q)]` at these scales for even `q<=32ell`. Use
`Q<=48u` in AT7 and normalize the error by `8au`. The exact ratio is
less than `0.000235425502` at `U`, and all summands decrease; the
exponential derivative condition is just `alpha sqrt u/2>5/2`.
The error is below `H/[4phi(q)]`, proving AT1b.

The source-domain comparison, rather than the error budget, is active.
At `U-1=13596` the source inequality fails, as checked with directed
rational logarithm bounds. This identifies the first integer base for
this sufficient source envelope; it is not a lower bound on prime supply
or on Sude's conjecture.

## 4. Proof for the actual entry modulus

For AS-small put `U_s=9000` and use the continuous modulus envelope


```math
Q\le Q_*(u)=200000+au,\qquad L_s(u)=\log Q_*(u).       \qquad\text{(ASs1)}
```


Indeed, the lifted moduli are below 200000, whereas the unlifted moduli
are at most `ell<=au`. The sum envelope avoids a case distinction at
the lift threshold. At the base the certificate proves


```math
U_s-1\gt 4R_1L_s(U_s)^2,\qquad
 \frac{40(U_s-1)}{\sqrt{Q_*(U_s)}L_s(U_s)^2}\gt 2.         \qquad\text{(ASs2)}
```


Both inequalities persist. For the first, the logarithmic derivative of
`(u-1)/L_s^2`, multiplied by `u`, is
`u/(u-1)-2au/[Q_*L_s]>1-2/L_s>0`. For the second, the corresponding
quantity is
`u/(u-1)-au/(2Q_*)-2au/(Q_*L_s)>1/2-2/L_s>0`.
The checked domain `L_s>4` persists. BMOR's exceptional-zero bound
therefore gives a signed main derivative greater than
`3/[4phi(Q)]`, since `exp(2)>4`.

Using `b+c<=4Y`, AT2 gives exponential error at most


```math
f_s(u)=4Q_*(u)\left(\frac{c_s\alpha\sqrt u}{2}+4\right)
                     e^{-\alpha\sqrt u}               \qquad\text{(ASs3)}
```


after the same normalization. The bounds `Q_*<288u^2` and
`L_s<u` hold at the base and persist; hence AT3 also applies. The
certificate gives


```math
200000[f_s(U_s)+r(U_s)]\lt 0.181083444776\lt 1.              \qquad\text{(ASs4)}
```


The logarithmic derivative of `f_s`, multiplied by `u`, is less than
`3/2-alpha sqrt(u)/2<0`; the two remainder terms also decrease.
Thus the error is below `Y/(200000phi(q))<=H/[4phi(q)]` throughout
the tail. Subtracting it leaves the claimed half main density (ASs).

For a reflected-bin controller the square composition must check `q<=ell`
at each bin's own center and `log Y>=9000` at the smallest center. These
conditions are not consequences of a target-scale bound alone. The global
entry supply may use its own center, for example `Y=X/2`, and must pass
the same checks separately.

## 5. Certificate and scope

Executable replay details are recorded in [Provenance](../PROVENANCE.md#optimized-bound).

The implementation uses integer arithmetic and fractions only. Its
logarithm, square-root, and exponential enclosures are the pinned earlier
implementations. It checks 18 target and 13 macro comparisons, including
the continuous persistence conditions, and runs ten rejection controls.
The source map must have exactly the required file set, lowercase
64-character SHA-256 values, and nonempty regular nonsymlink files whose
contents match those hashes. Missing, extra, empty, malformed, or mismatched
map entries are rejected. The complete campaign manifest additionally binds
this manuscript and its code.

The certificate verifies finite inequalities and the source bindings. The
analytic imports, the corrected explicit-formula argument, and the calculus
and combinatorial deductions remain mathematical proof obligations for
independent ordinary review. This is not an end-to-end kernel-checked
theorem. A successful result here must still be composed with exact input
pool conservation, both diagonals, the full odd-order tail, and all finite
controller and target hypotheses.

[Manuscript index](../README.md) · [Optimized theorem](../optimized-bound.md) · [Source and review record](../PROVENANCE.md#optimized-bound)
