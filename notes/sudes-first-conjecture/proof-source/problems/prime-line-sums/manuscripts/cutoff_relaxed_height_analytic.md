# Re-estimating the parameterized zero sums at a fixed minimum height

Author: `/root/analytic`. This additive argument preserves the
[original-domain linear-window theorem](cutoff_linear_window_analytic.md)
as an independent fallback. The new mathematical obligation is the
zero-sum lemma ZH0 below. Its proof uses the parameterized calculations
underlying BMOR Lemmas 6.8–6.9; those published lemmas are **not** invoked
outside their stated domain. The source-height question was proposed by `/root`; the explicit
epsilon bounds and elementary high-zero integral estimate were derived here.
`/root` checked the latter during collaboration and is not treated as a
nonauthor reviewer of this analytic extension.

Independent nonauthor review of this exact source is required before the
new supply profile is used as an established input. The
[arithmetic certificate](../code/cutoff_relaxed_height_analytic.py)
verifies the finite inequalities and their source bindings. It does not
establish the imported analytic results or kernel-check this proof.

## 1. Primary-source audit

The relevant primary sources are:

- [Bennett–Martin–O'Bryant–Rechnitzer, journal PDF](https://personal.math.ubc.ca/~gerg/papers/downloads/EBPAP.pdf):
  Definition 2.4 and Proposition 2.5, printed p.441; Proposition 1.11,
  p.436; the parameter definitions (6.20) and proof of Lemma 6.8,
  pp.499–500; the proof of Lemma 6.9, p.501; Lemma 6.11, p.503.
- [McCurley, *Explicit estimates for the error term in the prime number
  theorem for arithmetic progressions*](https://www.ams.org/mcom/1984-42-165/S0025-5718-1984-0726004-6/S0025-5718-1984-0726004-6.pdf):
  Lemmas 3.7–3.8 and their proofs, printed pp.276–280, especially
  (3.22)–(3.34) and (3.35)–(3.40).

The latter PDF, previously blocked on direct retrieval in this campaign,
became readable through the indexed primary-source record. Its full
parameterized low- and high-zero proofs were inspected for this extension.
Their conditions involve the monotonicity of the functions being integrated
and `H>=1`; the later simplification `alpha>=1` is not necessary for those
calculations. We verify the needed monotonicity below rather than infer it
from the original domain of BMOR's final lemma.

The corrected primitive-character explicit formula remains the one in
[effective_pair_supply.md](effective_pair_supply.md). No change is made to
`psi(t,chi)=psi(t,chi*)-J_chi(t)`, the deleted-prime-power bound, or the
critical-strip zero convention. Positive padding originally allowed for
Euler-factor zeros in McCurley's zero-sum bounds may be retained when
bounding the smaller critical-strip sums; it is not a new zero-set identity.

## 2. New zero-sum domain

Write

\[
 R=9.645908801,\quad C_1=0.399,\quad C_2=5.338,
 \quad \nu=\sqrt{\log x/R},\quad L=\log Q,
 \quad \eta=\nu/L-1,\quad \mathcal H=e^\nu/Q=Q^\eta.
\]

**ZH0.** Suppose `Q>=100000` and `mathcal H>=100000`, equivalently

\[
 \boxed{\log x\ge R\bigl(\log Q+\log100000\bigr)^2}.   \tag{ZH0a}
\]

For every character modulo `Q`, with the critical-strip zero set used in
the corrected E2 proof, the sum over zeros with `|Im rho|<=mathcal H`,
excluding a possible exceptional zero `beta_0`, is less than

\[
 0.5001\,\nu e^{-\nu},                                \tag{ZH0b}
\]

after weighting each zero by `x^(Re rho-1)/|rho|`. The corresponding
high-zero sum, with denominator `|rho(rho+1)(rho+2)|`, is less than

\[
 0.511\,\nu e^{-\nu}\mathcal H^{-2}.                  \tag{ZH0c}
\]

Consequently, for every even `Q` in this domain and every reduced class,
the sharper signed error (AL3) still holds:

\[
 |\theta(x;Q,a)-M_{Q,a}(x)|\le
 1.012x\nu e^{-\nu}
 +\frac{4Qxe^{-\nu}}{\varphi(Q)}
 +2\log Q\log x+Q\log Q+2\sqrt x.                     \tag{ZH0d}
\]

The exceptional main term is retained with its actual sign. The new domain
does not imply the absence of an exceptional zero.

### 2.1. Conditions before the numerical epsilon estimates

We have `nu>=2log100000>23`, `0<L<nu`, and `eta>0`. In McCurley's
notation take `lambda=(1+eta)^2`, so `log x=lambda R L^2`.
For the low-zero calculation, the function

\[
 t^{-1}\exp[-\nu^2/\log(Qt)]
\]

is increasing for `1<=t<=mathcal H`: its logarithmic derivative,
multiplied by `t`, is `-1+nu^2/log(Qt)^2>=0`.
For the high-zero calculation with `m=2`, the corresponding function
with `t^{-3}` decreases for `t>=mathcal H`, since that derivative is
`-3+nu^2/log(Qt)^2<=-2`. These are precisely the two parameter
inequalities used in (3.31) and in the integration following (3.40).

The conductor must be kept distinct from the ambient modulus in that
integration. If the primitive conductor is `Q_*`, write
`F_*(t)=(t/pi)log(Q_*t/(2pi e))` and
`R_*(t)=C_1 log(Q_*t)+C_2`. The two-sided estimate from Proposition 2.5
is `|N(t)-F_*(t)|<R_*(t)`. McCurley's (3.31) keeps this `F_*` inside
the Stieltjes integration by parts. Only afterwards are
`R_*(t)<=R_Q(mathcal H)` and `F_*(1)<=F_Q(1)` used. There is no
two-sided assertion with `Q_*` silently replaced by `Q`.

The low zeros of height at most one, after omitting the exceptional pair
as in BMOR's proof, also obey the needed monotonicity in their real parts:
the zero-free bound gives `Re rho>=1/(RL)>1/log x` because `nu^2>L`.
The boundary cancellation in McCurley's (3.32)–(3.33), after using BMOR's
zero-counting constants, follows from

\[
 (C_1-1/\pi)RL>2C_1.                                 \tag{ZH1}
\]

The certificate checks the stronger comparison with `1/pi` replaced by
`1/3` at `L=log100000`; it persists for larger `L`. The other hypotheses
used there are `Q>=10` and `mathcal H>=1`, both amply satisfied. Removing
the exceptional pair is exactly the modification already made in the
first comparison of BMOR Lemma 6.8; its reflected zero is restored below.
In particular, the full `N(1)` may still upper-bound the number of
ordinary low zeros in (3.28). The Stieltjes measure at heights greater
than one is unchanged by removal of a real exceptional pair. Equivalently,
subtracting two from both `N` and `F_*` preserves their difference and
can only decrease the low endpoint contribution. Thus this exclusion
introduces no unpaid positive counting-error term.

Thus the intermediate epsilon bounds displayed in the proofs of BMOR
Lemmas 6.8–6.9 follow from the same parameterized calculation here. Their
subsequent estimates must be redone: that is the purpose of the next two
subsections.

### 2.2. Low zeros, including the reflected exceptional zero

The bound before estimating the three terms is
`epsilon_2+epsilon_3+epsilon_4`, excluding both exceptional real zeros.
In terms of the present variables, BMOR's displayed expressions give

\[
\begin{split}
 \epsilon_2<&\ e^{-R\nu^2}(QL+\eta L^2)\\
 &+\tfrac12e^{-R\nu^2/2}
 \left[\frac{(1+4\eta+\eta^2)L^2}{2\pi}
       +\frac{(2+\eta)L}{\pi}
       +\frac{C_1\nu+C_2}{\mathcal H}
       +0.798L+11.075\right],\\
 \epsilon_3=&\ \frac{C_1\nu+C_2}{\mathcal H}e^{-\nu},\\
 \epsilon_4<&\ \tfrac12\int_1^{\mathcal H}
       t^{-1}e^{-\nu^2/\log(Qt)}\log(Qt)\,dt
       <\tfrac12\nu e^{-\nu}.                        \tag{ZH2}
\end{split}
\]

The last substitution, `s=nu^2/log(Qt)`, integrates from `nu` to
`nu^2/L` and then extends the upper endpoint to infinity. It requires
only `L<nu`, not `L<=nu/2`.

For `nu>=23`, the following elementary bounds apply:

\[
 \eta L^2\le\nu^2/4,\quad
 (1+4\eta+\eta^2)L^2\le3\nu^2/2,\quad
 (2+\eta)L\le2\nu,
 \quad Q<e^\nu.
\]

Also `(C_1 nu+C_2)/mathcal H<nu`, `0.798L<nu`,
`11.075<nu/2`, and `e^nu<e^(R nu^2/2)`.
With `pi>3`, these bounds give

\[
 \epsilon_2<
 \left(\frac38\nu^2+\frac{31}{12}\nu\right)e^{-R\nu^2/2}
 <\nu^2 e^{-R\nu^2/2}.                                \tag{ZH3}
\]

The normalized envelope `nu exp(nu-R nu^2/2)` decreases for
`nu>=23`. At 23 its exponent denominator exceeds `exp(2000)>2^2000`,
so it is less than `10^-6`. Moreover

\[
 \frac{\epsilon_3}{\nu e^{-\nu}}
 \le\frac{C_1+C_2/23}{100000}<10^{-5}.                 \tag{ZH4}
\]

If the reflected exceptional zero `1-beta_0` is present, then
`beta_0>0.99` because `RL>100`. BMOR Proposition 1.11 gives

\[
 \frac{x^{-\beta_0}}{1-\beta_0}
 \le \frac{e^{\nu/2}\nu^2}{40}\,e^{-0.99R\nu^2}.
\]

After division by `nu exp(-nu)`, this is bounded by the same
`nu exp(nu-R nu^2/2)<10^-6`; use
`0.49R nu>1/2`. Adding ZH2–ZH4 and this reflected term yields
`(1/2+10^-5+2*10^-6)nu exp(-nu)<0.5001nu exp(-nu)`.
This proves ZH0b without absorbing the exceptional zero itself.

### 2.3. High zeros and an elementary integral bound

The high-zero calculation gives `epsilon_5+epsilon_6+epsilon_7`, with

\[
\begin{split}
 \epsilon_5<&\ \frac{e^{-R\nu^2/2}}{2\mathcal H^3}
   \left(\frac{\mathcal H\nu}{2\pi}+0.798\nu+10.809\right)
    +\frac{4L e^{-R\nu^2}}{\mathcal H^2},\\
 \epsilon_7=&\ \frac{C_1\nu+C_2}{\mathcal H^3}e^{-\nu}.
                                                               \tag{ZH5}
\end{split}
\]

After normalization by `nu exp(-nu)mathcal H^-2`, the first is less
than `5exp(nu-R nu^2/2)<10^-6`, and the second is bounded by ZH4.
All decreasing-envelope and base comparisons are exact certificate inputs.

The remaining integral, after combining its two terms using
`C_1/t<log(2pi)` for `t>=mathcal H`, is at most

\[
 \epsilon_6<\frac12\int_{\mathcal H}^\infty
       t^{-3}e^{-\nu^2/\log(Qt)}\log(Qt)\,dt
 =\frac{Q^2}{2}\int_\nu^\infty s e^{-2s-\nu^2/s}\,ds. \tag{ZH6}
\]

Here is a direct bound for that integral, avoiding any unstated Bessel
function parameter domain. Let `f(s)=2s+nu^2/s`. For `s>=nu`,
`f'(s)>=1`. If `z=nu^2/s^2` lies in `[0,1]`, then

\[
 \left(\frac{s}{f'(s)}\right)'
   =\frac{2-3z}{(2-z)^2}\le\frac12,
\]

because `2-3z<=(2-z)^2/2`. Integration by parts therefore gives

\[
 \int_\nu^\infty s e^{-f(s)}ds
 \le\nu e^{-3\nu}+\frac12\int_\nu^\infty e^{-f(s)}ds
 \le(\nu+1/2)e^{-3\nu}.                               \tag{ZH7}
\]

Since `Q^2e^-2nu=mathcal H^-2`, the normalized epsilon_6 is at most
`1/2+1/(4nu)<=1/2+1/92`. Adding `10^-5+10^-6` gives a number strictly
below `0.511`, proving ZH0c.

### 2.4. Preserve the primitive normalization and all remainders

In the corrected E2 smoothing argument use
`h=2x/mathcal H` and `delta=2/mathcal H`.
The exact combined spectral coefficient is

\[
 0.5001(1+2/\mathcal H)
 +0.511(1+6/\mathcal H+18/\mathcal H^2+20/\mathcal H^3)
 <1.012.
\]

The inequality is checked at `mathcal H=100000` and persists.
The positive double average displaces its principal and exceptional
functions by total at most `2h/phi(Q)`, giving
`4Qx exp(-nu)/phi(Q)`. This is exactly AL3's mean-displacement argument.
The averaging domain remains inside `(2,2x)`, and the primitive remainder
and deleted Euler-factor powers need only that domain and `Q>=100000`.
Finally `log x=R nu^2>1500>500log10`, preserving the original domain
of BMOR Lemma 6.11 when prime powers are removed. Hence every remainder
in the corrected E2 proof is still paid, and ZH0d follows.

## 3. New linear target profile

Let `u=log Y`, `ell=ceil(log_2Y)`, `D=Y/ell`, and
`F=ell(7+2ceil(log_2ell))^2`. The same conclusion AT1a holds for
every even `q<=(369/1000)ell^2` and every `(b,c]` inside
`[Y-D,Y+D]` with `H>=D/2`, provided

\[
 \boxed{\log Y\ge11650}.                              \tag{ZH8}
\]

The strong initial-pair conclusion AT1b also holds there for `q<=32ell`.
No controller or square theorem is implied by this analytic-scale statement.

Retain `a=1443/1000`, `alpha=3219/10000`, `c_y=2001/1000`,
`C=369/1000`, and every rounding, exceptional-derivative, and error
envelope of the linear-window proof. The only changed source-domain
inequality is

\[
 U-1>R\,[L(U)+\log100000]^2,
 \quad L(u)=\log(Ca^2)+2\log u.                        \tag{ZH9}
\]

It has margin exceeding `2981.833622475794` at `U=11650`.
The ratio `(u-1)/(L(u)+log100000)^2` increases because its denominator's
logarithm term exceeds 4. Thus ZH0 applies at every endpoint on the tail.
The fixed main coefficient computed at this base is

\[
 A=\frac{5321071}{125000},\qquad
 A-\tfrac12=\frac{5258571}{125000}.
\]

The complete normalized weak error is less than `0.998854483492`;
the strong-target error is less than `0.002644173218`. The exact
derivative inequalities from AT8 persist with the smaller base. Thus the
remaining theta weight and conversion to `H/(qF)` are unchanged.
The weak error budget is now the active sufficient inequality.
The checker rejects `U=11649` under these same envelopes; this rejection
is not a lower bound on the mathematical prime-supply statement.

## 4. Centered entry intervals

An independent consequence of the original-domain AL3, requiring no use
of ZH0, is useful for the reflected bins:

**AS-centered.** If `log Y>=7400`, `q` is even, `2<=q<=ell`, and
`(b,c]` lies in `[Y/2,2Y]` with `b+c=2Y` and `H=c-b>=Y/32000`,
then every reduced class modulo `q` has prime count at least
`H/[2phi(q)log(2Y)]`.

Use the same envelope `Q_*(u)=200000+(1443/1000)u` as AS-small.
The original source domain `u-1>4R log^2Q_*` and the exceptional
main-derivative bound greater than `3/[4phi(Q)]` both hold at 7400
and persist by the same derivatives. Because `b+c=2Y`, the exponential
error is half of ASs3. Normalizing it and AT3 by 128000, rather than
200000, gives at most `0.914982936615` at the base. Every summand
decreases on the tail. The error is below `H/[4phi(q)]`, proving the
statement. This covers both symmetric reflected bins and the global entry
interval centered at `X/2`, once the square composition verifies their
individual scale and modulus conditions.

## 5. Reproduction and boundary of the claim

Run

~~~sh
python3 -B problems/prime-line-sums/code/cutoff_relaxed_height_analytic.py
~~~

There are 16 exact checks for the height lemma, 18 for its target
specialization, 13 for the centered-macro corollary, and ten rejection
controls. The seven-file required dependency map includes the original
linear-window fallback and rejects missing, extra, malformed, empty,
nonregular, or mismatched source inputs. All rational enclosures and
continuous-envelope derivatives are recorded in code or the proof above.

The genuinely new obligation is ZH0's extension of the parameterized
zero-sum calculation, including its handling of the exceptional pair.
Ordinary independent review must inspect that derivation and the primary
source conditions. The code cannot discharge it. The original-domain
`U=13597` profile remains reproducible even if ZH0 is not accepted.
The complete campaign must additionally certify the finite target and
controller construction, entry conservation, both diagonals, exact integer
rounding, and translation to every sufficiently large odd order.
