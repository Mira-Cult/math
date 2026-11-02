# Exact prime target lists by a repeated-target reservoir

This finite lemma supplies the exact-total prime vectors used in the
[explicit-bound proof](explicit-bound.md). Its progression hypotheses are
proved by [S40-W and S40-S](classical-primes.md). Repetitions of line-sum
targets are permitted: unlike array entries, targets do not consume the
prescribed prime pool. Every local combinatorial step is proved here.

## Finite target-list lemma

Let $y,D>0$ and let $\ell=\lceil\log_2y\rceil\ge2$.
Let $g$ be even, $2\le g\le16\ell$, and let $a_1,\ldots,a_k$ be
reduced residue classes modulo $g$. Suppose:

1. $T=ky$ is an integer and $\sum_i a_i\equiv T\pmod g$.
2. $D\le y/4$, $D\ge2^{20}\ell^{11}$, and $k\ge54000\ell^{11}$.
3. In each reduced class modulo $g$, every interval $I\subset[y-D,y+D]$
   of length at least $D/500$ contains at least $|I|/(4g\ell)$ primes.
4. For every integer $2\le q\le128\ell^2$, in each reduced class modulo
   $q$, every such interval contains at least $|I|/(4q\ell^9)$ primes.

Then there are primes $t_i$, with repetitions permitted, such that

$$
 t_i\equiv a_i\pmod g,\qquad |t_i-y|\le D,\qquad \sum_i t_i=T.
$$

### 1. Find a small repeatable difference

Some class $a$ occurs at least $k/g$ times. In
$[y-D/4,y+D/4]$, hypothesis 3 supplies $M_0\ge D/(8g\ell)$
primes in this class. Since $M_0\ge2$, two consecutive primes $r<s$ have

$$
 h=s-r\le D/M_0\le8g\ell\le128\ell^2.
$$

Indeed, the span of all $M_0$ primes is at most $D/2$, and
$M_0-1\ge M_0/2$. The even integer $h$ is a multiple of $g$.
All primes in the window exceed $h$: $y\ge4D$, the window's lower
endpoint is at least $15D/4$, and $D\ge2^{20}\ell^{11}>128\ell^2$.
Thus $b=r\pmod h$ is reduced and lifts $a\pmod g$.
The same pair $(r,s)$ may be used in arbitrarily many target coordinates.

### 2. Complete an h-grid interval with a bounded number of slots

Put $F=4\ell^9$. Let $A$ be the primes in class $b\pmod h$ in
$[y-D/2,y+D/2]$. Hypothesis 4 gives $M=|A|\ge D/(hF)$.
Use $s_0=4F=16\ell^9$ copies of the seed pair. Their differences cover
the $h$-grid from 0 to $R_0=s_0h$, and

$$
 4D/M\le R_0\le2048\ell^{11}\le D.
$$

For $R_0\le R\le D$, divide the interval containing $A$ into
$\lceil D/R\rceil\le2D/R$ bins of length at most $R$. One bin
contains at least $MR/(2D)\ge2$ points. The difference $d$ between
its extremes is an $h$-multiple satisfying

$$
 R/(4F)\le hMR/(4D)\le d\le R.
$$

For the middle inequality, if the bin contains $z\ge MR/(2D)\ge2$
points on an $h$-grid, its span is at least $h(z-1)\ge hz/2$.
If existing differences cover every $h$-multiple from 0 to $R$, appending
an $h$-multiple $d\le R+h$ preserves coverage from 0 to $R+d$:
the original interval and its translate by $d$ touch or overlap on the grid.
Thus appending this $d$ preserves complete coverage. Reuse of earlier
primes is harmless for these target slots.

Each group of $4F$ appended differences at least doubles $R$, since
$(1+1/(4F))^{4F}\ge2$ by the binomial theorem. At most $4F\ell$
appended stages therefore reach $R\ge D$, because $D\le y\le2^\ell$.
The resulting prefix uses at most

$$
 P\le4F(\ell+1)\le32\ell^{10}
$$

slots. Its endpoints lie in $[y-D/2,y+D/2]$, and its total difference
$R$ lies in $[D,2D]$. If $R_0=D$, no growth stage is needed.

### 3. Add capacity with centered pairs

Set $\delta=1/1000$. Hypothesis 4 gives a prime $u\equiv b\pmod h$ in
$[y-D/3-\delta D,y-D/3+\delta D]$, and a prime $v$ in the same
class in $[y+D/3-\delta D,y+D/3+\delta D]$. Both intervals have
length $D/500$, and their lower count exceeds one because
$D\ge2^{20}\ell^{11}$ and $h\le128\ell^2$. Therefore

$$
 D/2<v-u<D,\qquad |(u+v)/2-y|\le\delta D.
$$

Append $J=100(P+1)$ copies of this pair. Each is a legal grid extension
because the current endpoint is already at least $D$. Let $R_{\rm tot}$
be the total difference and $A_{\rm tot}$ the sum of the lower endpoints
of the $r_*=P+J$ controlled slots. Their possible sums contain every
$h$-grid point in $[A_{\rm tot},A_{\rm tot}+R_{\rm tot}]$, and

$$
 r_*\le3332\ell^{10},\qquad R_{\rm tot}\ge JD/2,
$$
$$
 |A_{\rm tot}+R_{\rm tot}/2-r_*y|\le PD/2+J\delta D.
$$

There are enough coordinates in the common original class $a$:
$k/g\ge3375\ell^{10}\ge r_*+3$. Reserve $r_*$ of them.
At least three coordinates remain unreserved.

### 4. Lift all remaining residues before choosing primes

Choose reduced classes $b_i\pmod h$ for the unreserved coordinates,
lifting their original classes $a_i\pmod g$, so that

$$
 \sum_{i\text{ unreserved}}b_i\equiv T-r_*b\pmod h.
$$

This is an elementary Chinese remainder statement. For $p^v\Vert g$
and $p^w\Vert h$ with $w\ge v$, the required total is already
compatible modulo $p^v$. Altering one lift by a multiple of $p^v$ achieves
the prescribed sum modulo $p^w$ without losing its unit property.
For a new prime $p\mid h$, $p\nmid g$; hence $p$ is odd.
Fix arbitrary units for all but three unreserved coordinates. Every residue
modulo $p^w$ is a sum of three units: choose the first unit to be 1, then
choose the second residue modulo $p$ different from 0 and from the desired
sum minus 1; the resulting third residue is also a unit. Choose lifts modulo
$p^w$ and use the Chinese remainder theorem over the prime powers of $h$.

This handles overlapping prime powers and does not assume that $g$ and
$h/g$ are relatively prime.

### 5. Greedy discrepancy and exact grid repair

For each unreserved $b_i$, hypothesis 4 supplies a prime on each side of
$y$ in $[y-D,y+D]$. Process these coordinates in any order. If the
running discrepancy $\sum(t_i-y)$ is nonnegative, choose the lower prime;
otherwise choose the upper prime. Induction keeps the discrepancy in
$[-D,D]$, independently of the number of coordinates processed.

The desired reserved sum is congruent to $A_{\rm tot}\pmod h$.
Its distance from $A_{\rm tot}+R_{\rm tot}/2$ is at most

$$
 D+PD/2+JD/1000<JD/4\le R_{\rm tot}/2,
$$

because $J=100(P+1)$. It lies on the covered grid, so choosing one endpoint
from each controlled pair realizes it. Every choice is prime, within $D$
of $y$, and in the originally assigned class modulo $g$. The total is
exactly $T$. This proves the lemma. $\square$

## Interface used for the explicit bound

The square construction takes

$$
 E=\lceil\log_2X\rceil,\quad K=\lfloor n/E^3\rfloor,\quad
 y=T/n,\quad \ell=\lceil\log_2y\rceil,\quad D=y/\ell^4.
$$

The [composition proof](explicit-bound.md#4-exact-prime-target-vectors-of-length-n)
checks every size and progression hypothesis uniformly for every odd
$n\ge2^{2^{40}}$. It applies the lemma separately to the $n$ row
residues and the $n$ column residues, each with exact total $T$.
Each diagonal needs one prime in its own reduced class and does not require
an additional total constraint. All these targets fit the controller's
transfer range. No target prime is added to the array as an entry.
