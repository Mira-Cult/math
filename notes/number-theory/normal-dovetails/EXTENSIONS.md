# Singular, flat, and near-polynomial source families

**Additional producer-proof drafts, reproduced for scrutiny.** These extend the [main manuscript](MANUSCRIPT.md). Their statements and full arguments are retained with exact scope, but this release does not upgrade their audit status. See [verification](VERIFICATION.md). The source is the corrected October 20 generalized-centers contribution recorded in [provenance](PROVENANCE.md).

The numbered sections and equation labels below retain the source numbering. All notation and the common schedule are defined in the main manuscript. The earlier balanced schedule used only for the suppression comparison is characterized by $K_r=O(r\log r)$ and $A_r-r\ge c r/\log r$; these two properties alone imply the stated suppression.

## 6. Singular powers on positive inputs

Consider `B(theta,y)=y^theta`, `g(x)=x/(1-x)` and `x>0`. Choose the positive real branch `y^theta=exp(theta log y)` for every real theta. Then

`h_theta(x)=x^theta (1-x)^(-theta)`.

**Theorem E.** There is one computable stage schedule of the form in Theorem A for which every fixed **theta != 0** produces a normal concatenation, all original rows and cutoffs included. For compact `J` avoiding the nonnegative integers, the discrepancy estimate of Theorem A is uniform on J. The positive integer parameters are also admitted by the analytic rational-derivative theorem, using the **same source schedule**, but a bound uniform while crossing those integers is not established here. At theta=0 the source equals 1 and every fractional digit is zero.

**Proof on compact J disjoint from nonnegative integers.** Set `u_theta(x)=(1-x)^(-theta)` and `p_k(theta)=theta(theta-1)...(theta-k+1)`. The quantity

`delta=min_(theta in J, l in Z_>=0)|theta-l|`

is strictly positive. Leibniz's formula gives, for `k>=1`,

`h_theta^(k)(x)=p_k(theta) x^(theta-k) u_theta(x) [1+E_(k,theta,x)]`,

where

`|E_(k,theta,x)| <= exp(C_J k^2 x/delta)-1`.     (6.1)

To check (6.1), divide the ell-th Leibniz term by the ell=0 term: the ratio of falling factorials contributes at most `delta^(-ell)`, while `u_theta^(ell)/u_theta=(theta)^(overline ell)(1-x)^(-ell)` contributes at most `(ell+C_J)^ell(1-x)^(-ell)`. Together with `binom(k,ell)<=k^ell/ell!` the sum is bounded by an exponential in `C_J k^2 x/delta`. Since `x<=b^(2-B_r)` and `k<=D_r+L1=O(log B_r)`, it is at most 1/2 for large r, uniformly on J. Thus the derivative has one sign. The lower product satisfies `|p_k(theta)|>=min(1,delta)^k`; the upper satisfies `|p_k(theta)|<=(k+C_J)^k`.

On the real source interval `b^(r-1)-1<=y<=b^r`, the input `x=(by+1)b^(-A_r)` lies between `b^(-B_r-1)` and `b^(2-B_r)` for large r. Consequently the variation ratio of the kth derivative is at most `6 b^(3(k+C_J))`. This is **not** a constant 3, but `log_b` of it is `O_J(k)=o(r)`. Taking `k=floor(t/(A_r-1))+L1` with a sufficiently large fixed `L1=L1(J)` gives `3<=k<=D_r+L1` for all sufficiently large r and all retained `t>=T_J B_r`. The floor gives precisely

`t-k r <= -(L1-1)r+O(D_r B_r)`,

because `floor(t/(A_r-1))>=t/(A_r-1)-1`; the stronger `-L1 r` is not justified. The existing large fixed L1 absorbs this one-unit loss, and `D_r B_r=o(r)`. First apply the derivative estimates to harmonic 1:

`lambda_1 m_full^k >= b^(t/2)`, `Lambda_1<=b^(-8r)`,

`Lambda_1/lambda_1 <= 6b^(3(k+C_J))`.     (6.2)

The lower estimate reflects cancellation of `x^(-k)` against the `b^(-k B)` factor: `log_b(lambda_1 m_full^k) = t - theta B_r + O_J(k log(k+2))`, uniformly on the interval. The upper follows from the corrected floor inequality and a sufficiently large L1. Choose `0<c_J<=1` small enough for the derivative saving, and put

`H_t=max(1,floor(b^(c_J min(t,r)/(8*2^(D_r+L1)))))`.

Then `H_t<=b^(r/8)`, so **only for `1<=h<=H_t`** one has `Lambda_h<=b^(-7r)`, `lambda_h m_full^k>=b^(t/2)`, and the same variation ratio as in (6.2). The three terms of the main manuscript, Appendix A are bounded by `b^(-c_J min(t,r)/2^k)` after decreasing c_J if needed; the first ratio's polynomial-in-B factor is paid by `m_full~b^r`. Repeating the geometric offset summation and exact all-prefix assembly in the main manuscript, §3 gives `O_J(N B_r/(rD_r))` for every fixed word.

For theta=m positive integer, `h_m(x)=x^m/(1-x)^m` is analytic at zero and has nonpolynomial rational derivative, so its Taylor coefficients satisfy (W1)-(W2). The universal schedule from the main manuscript, §3 applies without alteration, proving pointwise normality at these isolated parameters. For theta=0, `h_0=1`. Hence one schedule works for the full punctured real axis; claimed compact uniformity is restricted as stated. QED.

**Important distinction.** For negative theta the input function diverges as `x->0`, but its **fractional part** still obeys the phase derivative argument; singularity is not a proof of failure. At a positive integer, the fractional function itself is rational and admitted, whereas its leading singular-power derivative approximation vanishes and the separate analytic proof is needed. No claim that mere nonpolynomiality of an arbitrary nonsmooth germ suffices is made.

## 7. Exact inverse cancellations and suppression by schedule

For `g(x)=x/(1-x)`, the compositions

`B_1(y)=y/(1+y)=x`, `B_2(y)=1/(1+y)=1-x`

are exact polynomial identities. Likewise `exp(log(1+x))=1+x`. Integer-coefficient polynomial source values have at most `degree*A_r+O(W)` potentially nonconstant starts per copied row. All these examples therefore fail in this observation model at the stated fixed center for **every** admissible schedule with `D_r->infinity`. Invertibility and a nonzero first derivative are plainly insufficient.

**Theorem F (flat, schedule-dependent survival).** Fix `g(x)=x/(1-x)>0` for `0<x<1` and `B(theta,y)=exp(-theta/y)`, with real `theta!=0`. There exists one computable schedule independent of theta, satisfying all source limits, for which every fixed nonzero theta produces a normal output. Convergence is uniform on each compact interval avoiding zero. By contrast, under the earlier *balanced* schedule, which has `K_r=O(r log r)` and precision gap `B_r^(old)>=c r/log r` for some fixed `c>0`, the output for each fixed `theta>0` eventually consists entirely of zero copied rows. Thus suppression by one schedule is not impossibility for the operation.

**Proof.** The exact composite is `h_theta(x)=exp(theta-theta/x)`. Choose the following exact integer schedule, for sufficiently large r,

`B_r=3+min{m>=1: b^(b^m)>=r+4}`, `A_r=r+B_r`,

`D_r=max(1,floor((log_2 B_r)/8))`, with a bounded-increment smoothing of D; copy `K_r=A_rD_r` digits. The threshold comparisons involve integers only, so this schedule is computable without deciding equality of transcendental real expressions. Then `b^B_r=Theta_b(log r)` and `D_r->infinity`.

Write the logarithm of the source as `q(y)=theta-theta b^A/(by+1)`. Its first derivative is `q'(y)=theta b^(A+1)/(by+1)^2`, of sign theta, and its normalized higher derivatives satisfy

`|q^(ell)(y)|/|q'(y)|^ell <= ell! (C_b/(|theta| b^B_r))^(ell-1)`, `ell>=2`,

throughout the stage, with a fixed b-dependent constant. Expanding `d^k exp(q)/dy^k` by the elementary Bell partition formula, the sum of terms containing an ell>=2 block has relative magnitude at most

`exp(C_b k^2/(|theta|b^B_r))-1`.     (7.1)

For `k<=D_r+12=O(log B_r)` this is below 1/2 eventually, uniformly on `delta<=|theta|<=M`. Hence its kth derivative has the sign of `theta^k`, and is comparable to `exp(q)|q'|^k` by factors between 1/2 and 3/2. Since `|q|=O_(theta,b)(b^B_r)=O_theta(log r)` and `log_b |q'|=-r+B_r+O_(theta,b)(1)`, with stage variation bounded by `exp(O_theta(b^B_r))=r^(O_theta(1))`, the explicit choice `L=10` in

`k=floor(t/(A_r-1))+10`

supplies `3<=k<=D_r+10<=D_r+12` and, for `t>=T_theta b^B_r`, the harmonic-one bounds

`lambda_1 m_full^k >= b^(t/2)`, `Lambda_1<=b^(-8r)`,

`log_b(Lambda_1/lambda_1)=O_theta(log r)`.

Indeed `t-k r<=-9r+O(D_r B_r)` and the remaining logarithmic derivative terms are `O_theta(D_r B_r+log r)=o(r)`, leaving the claimed `-8r` margin. Choose `0<c<=1` small enough and

`H_t=max(1,floor(b^(c min(t,r)/(8*2^(D_r+12)))))`.

Since `H_t<=b^(r/8)`, the upper bound `Lambda_h<=b^(-7r)` is asserted **only for `1<=h<=H_t`**; in that range the same variation ratio and the lower bound `lambda_h m_full^k>=b^(t/2)` hold.

The order is at most D+12, the growing-order estimate in the main manuscript, Appendix A applies, and its three terms are bounded by `b^(-c min(t,r)/2^k)` for a fixed positive `c` once r is large. Offset-dependent Fejer cutoffs and summation as in the main manuscript, §3, with `T_theta b^B_r=O_theta(log r)` early offsets, give the all-prefix estimate

`|C_w(N;theta)-Nb^(-W)| = O_(theta,b,W)(N log r(N)/(r(N)D_(r(N))))`.     (7.2)

The constants and onset are uniform on compact subsets of `R\{0}`. On the earlier balanced schedule, `x_j<=b^(2-B_r^(old))`, so `0<h_theta(x_j)<=exp(theta-theta b^(B_r^(old)-2))` for theta>0. Under the two comparison bounds stated above, `K_r=O(r log r)` and `B_r^(old)>=c r/log r`, so `b^(B_r^(old))/K_r->infinity`. Hence this is eventually smaller than `b^(-K_r)` for every row, forcing its full K-digit block to zero. This suppression statement is restricted to that schedule; it does not cover arbitrary copied lengths allowed to grow faster than this exponential shrinkage. At theta=0 the source is the integer 1. QED.

**Reciprocal-square kernel, with the Bell estimate expanded.** For `B(theta,y)=exp(-theta/y^2)`, set

`z=by+1`, `a=b^A`, `v=a/z=1/x`, `q(y)=-theta(v-1)^2`.

Direct differentiation of `-theta(a^2 z^(-2)-2a z^(-1)+1)` gives, for every `ell>=1`,

`q^(ell)=(-1)^(ell+1) theta ell! b^ell z^(-ell) [(ell+1)v^2-2v]`.

In particular `q'=2theta(b/z)v(v-1)` has sign theta when `v>=2`. For `ell>=2`, using `2v(v-1)>=v^2` and `ell+1<=4^(ell-1)`,

`|q^(ell)|/|q'|^ell <= ell! [4/(|theta|v^2)]^(ell-1)`

`<= ell! [C_b/(|theta|b^(2B_r))]^(ell-1)`.

To justify the summed Bell remainder, write `eta=C_b/(|theta|b^(2B_r))`. In the complete Bell partition formula the leading term is `(q')^k`. Group all other terms by their number j of blocks. The normalized absolute sum is bounded by

`sum_(j=1)^(k-1) [k!/j!] binom(k-1,j-1) eta^(k-j)`

`<= sum_(s=1)^(k-1) (k^2 eta)^s/s! <= exp(k^2 eta)-1`.

The coefficient in the first sum is the unsigned Lah number: it follows by taking k! times the coefficient of degree k in `exp(sum_(ell>=1) eta^(ell-1) u^ell)` in a formal variable u. Thus the relative remainder is at most

`exp(C_b k^2/(|theta|b^(2B_r)))-1`,

uniformly on compact parameter sets avoiding zero. This also justifies (7.1) with `eta=C_b/(|theta|b^B_r)` for the reciprocal kernel.

Choose

`B_r=3+min{m>=1: b^(b^(2m))>=r+4}`, `A_r=r+B_r`,

and the same bounded-increment depth with `k<=D_r+12`. This threshold again uses integer comparisons only. Then `b^(2B_r)=Theta_b(log r)`, the Bell remainder tends to zero, `|q|=O_theta(log r)`, and `log_b|q'|=-r+2B_r+O_theta(1)`. The same `k=floor(t/(A_r-1))+10` gives `Lambda_1<=b^(-8r)` and `lambda_1 m_full^k>=b^(t/2)` after discarding `O_theta(log r)` offsets; `D_r B_r=o(r)` pays the extra `2k B_r`. With the preceding `H_t`, `Lambda_h<=b^(-7r)` for `1<=h<=H_t`, and the variation logarithm is `O_theta(log r)`. The derivative estimate, offset sum and all-prefix assembly therefore give (7.2) for this kernel as well. **This is a second flat-kernel instance, not a blanket theorem for arbitrary C-infinity flat operations.**

## 8. Carry-aware near-exception estimates

Here `theta` remains fixed along each output, but in a **triangular comparison** we may choose a different parameter for a different output cutoff N; these are distinct infinite outputs, not row-varying theta_j. Fix a nonnegative integer m, a regular stage schedule in the main manuscript, §3 with `K_(r-1)/K_r -> 1`, and `alpha=m+epsilon` where `0<|epsilon|<=1/2`. Let `E(epsilon)=max(0,log_b(1/|epsilon|))`. Offsets are zero-based: offset t starts at digit t+1, and a within-row word must satisfy `t<=K_r-W`. The sign of epsilon is held fixed when taking a sign-specific subsequence.

**Proposition G (sharp scale for this schedule).** For any family `epsilon_N` with `0<|epsilon_N|<=1/2`, the triangular word frequencies of the outputs generated from `h_(m+epsilon_N)(x)=(1+x)^(m+epsilon_N)` satisfy

`C_w(N;m+epsilon_N)/N -> b^(-|w|)` for every fixed w

**if and only if** `E(epsilon_N)/K_(r(N)) -> 0`. The analogous statement holds in family (ii) with `theta=-m+epsilon_N`, so the actual exponent is `m-epsilon_N` and the source is `(1-x)^(m-epsilon_N)`. In this convention positive epsilon again gives a positive perturbation and zero words, and negative epsilon gives borrowed `(b-1)` words. The parameters are not allowed to vary within one output.

**Sufficient direction.** For derivatives of order `k>m`, the exact identity

`d^k/dx^k (1+x)^(m+epsilon) = (m+epsilon)_(fall k)(1+x)^(m+epsilon-k)`

has magnitude bounded above and below, on `0<=x<=b^(2-B_r)`, by `|epsilon| exp(+-C_m k log(k+2))`, with the ratio of the maximum to minimum bounded uniformly when `|epsilon|<=1/2` and k exceeds m+2. Choose explicitly `L_m>=max(m+3,12)` and `k=floor(t/(A_r-1))+L_m`, so **every chosen derivative order exceeds m**, and `k<=D_r+L_m` at all sufficiently large stages. The whole high-derivative Taylor remainder retains the epsilon factor: define

`R_epsilon(x)=((1+x)^(m+epsilon)-(1+x)^m)/epsilon`.

This has a uniformly bounded analytic derivative on a fixed interior disk for `|epsilon|<=1/2`, extending continuously at epsilon=0. For every coefficient index `n>=m`, `c_n(epsilon)=epsilon a_n(epsilon)` with `|a_n(epsilon)|<=M_m S_m^n`. Since `k>m`, all coefficients in the derivative remainder have that form, and (3.1) becomes

`|h^(k)(x)/(k-1)!-c_(k-1)(epsilon)| <= |epsilon| 4 M_m k S_m^k x`.

Thus the relative remainder estimate has no spurious factor `1/|epsilon|`. Equivalently the exact derivative identity above supplies the same uniform sign and variation bounds. The growing derivative calculation in the main manuscript, §3 works after discarding `O_m(B_r+E(epsilon))` actual offsets: take `t>=T_m B_r+2 E(epsilon)` with a sufficiently large fixed T_m. The lower bound needed is the safe one

`lambda_1 m_full^k>=b^(t/16)`.

The harmonic-one upper bound is `Lambda_1<=b^(-8r)`; with an offset-dependent cutoff as in the main manuscript, §3 (and a sufficiently small fixed saving constant), `Lambda_h<=b^(-7r)` only for `1<=h<=H_t`. Fourier and harmonic summation pay `O_m(B_r+E+2^D)` starts per row and the same ambient-row bill. This bound is harmless even if the retained range is empty: charge the row trivially, at most the discarded-offset bill. Summing with geometric row counts gives, for all prefixes with r large and `E=o(K_r)`,

`|C_w(N;m+epsilon_N)-Nb^(-W)|/N <= O_(m,b,W)(B_r/(rD_r)+E(epsilon_N)/K_r)+o(1)`.     (8.1)

For family (ii), replace the numerator defining R_epsilon by `(1-x)^(m-epsilon)-(1-x)^m`; the same analytic epsilon factor and derivative argument apply.

This uses exact phases and Fejer intervals, so **no** numerical digit-stability assumption is made near a carry boundary.

**Necessary direction and the borrow.** Let `P_m(x)=(1+x)^m` and `Delta=(1+x)^(m+epsilon)-P_m(x)`. For 0<x<=1/2 and `|epsilon|<=1/2`,

`0<|Delta|<=C_m |epsilon| x`, `sign Delta=sign epsilon`.

For row j in a late stage, `P_m(x_j)` is a rational polynomial with denominator dividing `b^(m A_r)` and `x_j<=b^(2-B_r)`. At offsets `t>=m A_r`, `b^t P_m(x_j)` is an integer. Fix `C_star>2+log_b C_m`. For any actual within-row offset satisfying

`m A_r<=t<=K_r-W`, `t+W<=E(epsilon)+B_r-C_star`,

one has `b^t P_m(x_j)` integer and the strict bound

`0<b^t|Delta|<=C_m b^(t-E+2-B_r)<b^(-W)`.

For epsilon>0 the fractional part of `b^t(P_m+Delta)` lies in the cylinder of W zeros. For epsilon<0 it is `1-b^t|Delta|` and lies strictly inside the cylinder of W digits `b-1`: this is the **borrow**, with strict endpoint slack. This proves a digit statement at a terminating rational endpoint, not a general inference from closeness of two reals. The number of forced constant-word starts per row is at least

`max(0, min(K_r,E+B_r-C_star-W)-m A_r-O(W))`.     (8.2)

If `limsup E(epsilon_N)/K_(r(N))>0`, pass to a sign-constant subsequence with `E>=rho K_r`. The regular schedule gives `N<=C_b b^r K_r`. Because `D_r->infinity`, `m A_r=o(K_r)`, `B_r=o(K_r)`, `K_(r-1)/K_r->1`, and the **entire previous stage** is present at every such cutoff, (8.2) forces a positive fraction `eta(rho,b)>0` of its starts to be the same constant word of any fixed length W. The preceding-stage proportion is bounded below independently of each fixed W; using `K_(r-1)/K_r->1`, its forced length is at least `min(1,rho)K_(r-1)/2` eventually. Choosing one fixed W with `b^(-W)<eta/2` contradicts normality. Thus `E/K_r->0` is necessary. In family (ii), `Delta=(1-x)^(m-epsilon)-(1-x)^m` also has sign epsilon and `0<|Delta|<=C_m|epsilon|x`, so the same integer-endpoint and borrow proof applies with this stated parameter convention. The proof uses a *long constant word*, not merely an excess of single zeros that might in principle be compensated elsewhere. QED.

For a **fixed** epsilon!=0, `E` is constant and the criterion gives survival. For `epsilon_N` exponentially small in K, a positive density of long constant blocks survives. This is a scale threshold for these specified outputs, **not** a classification of all imaginable schedules or a theorem about parameter sequences theta_j varying from row to row.

