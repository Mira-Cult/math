# Transfer, source-count obstructions, and transcendence

These elementary arguments connect the older dovetail constructions to the newer analytic admission theorem. Claim labels retained from the October 16 reference edition serve as locators, not as priority claims. The classical de Bruijn and Liouville construction is included for context; computable absolutely normal Liouville numbers were already constructed by Becher, Heiber and Slaman (2014). See [references](REFERENCES.md).

Normality of a constructed output does not prove normality of its center. Ordinary convergence of source values does not supply the shifted orbit comparison required below. Likewise, function-theoretic transcendence and transcendence of a number are distinct questions.

Throughout, $b\ge2$ is an integer, $e(t)=\exp(2\pi i t)$, $\mathbb T=\mathbb R/\mathbb Z$, and $\lVert t\rVert =\operatorname{dist}(t,\mathbb Z)$. All digit expansions use the terminating convention at radix-rational endpoints.

## Average orbit distance

**CON-005.** The set
```math
\mathcal H_b=\left\lbrace z\in\mathbb T:
\frac1N\sum_{n<N}\lVert b^nz\rVert \longrightarrow0\right\rbrace 
```
is an additive subgroup. If $x-y\in\mathcal H_b$, every fixed integer character has the same limiting averages along the two radix orbits whenever either limit exists. In particular, $x$ is normal if and only if $y$ is normal.

**Proof.** The circle triangle inequality gives closure under addition, and $\lVert -z\rVert =\lVert z\rVert$ gives closure under inverses. Also
```math
|e(hb^nx)-e(hb^ny)|\le2\pi|h|\lVert b^n(x-y)\rVert .
```
Averaging and applying the Weyl criterion proves the conclusion. $\square$

This is a valid statistical equivalence relation. It does not make the set of normal numbers a subgroup: for any normal $x$, both $x$ and $-x$ are normal while their sum is zero.

**CON-006.** Suppose a real $F$ is made by concatenating complete prefixes, of lengths $K_j$, of source numbers $s_j$. Put $S_j=\sum_{i\le j}K_i$. For a prescribed target $C$, define
```math
\delta_j=\lVert b^{S_{j-1}}C-s_j\rVert ,
\qquad \ell_j=-\log_b\delta_j
```
with $\ell_j=+\infty$ if $\delta_j=0$. Assume the number of rows is $o(N)$, the terminal row is negligible $K_j/S_{j-1}\to0$, and
```math
\sum_{j\le J}(K_j-\ell_j)_+=o(S_J).
\tag{7.1}
```
Then $C-F\in\mathcal H_b$. Hence normality of $F$ transfers to $C$.

**Proof.** The output and its row source have the same first $K_j$ digits at the row start. At local time $0\le r<K_j$, their circle distance is at most $b^{r-K_j}$; summing this bound gives at most $1/(b-1)$ for that row. For the target and source, multiplication by $b$ is $b$-Lipschitz on the circle, so the distance at time $r$ is at most $\min(1/2,b^r\delta_j)$. A geometric series up to $r\approx\ell_j$, followed by the trivial bound, yields
```math
\sum_{r<K_j}\min(1/2,b^r\delta_j)
\le C_b+(K_j-\ell_j)_+.
```
The row triangle inequality, (7.1), and the $o(N)$ row count prove zero mean distance at row endpoints. An incomplete terminal row costs at most $K_j/2=o(N)$, proving the same for every prefix. $\square$

The start $b^{S_{j-1}}C$ is essential. Replacing it by the unshifted $C$ changes the assertion. Ordinary numerical convergence $s_j\to C$ gives no such shifted shadowing estimate.

## An exact arithmetic grid for logarithmic sources

This local calculation explains the arithmetic engine of the gist's uniform logarithmic constructions without treating the center as normal.

**CON-007.** Fix integers $D\ge d\ge2$, let $L_d=\operatorname{lcm}(1,\ldots,d)$, and let $A$ be a positive multiple of $L_D$. Put
```math
n_j=bj+1,\quad x_j=n_jb^{-A},\quad
F_d(z)=\sum_{k=1}^d\frac{(-1)^{k-1}z^k}{k}.
```
Let $B$ be a nonnegative integer satisfying $k_{(b)}\mid b^B$ for all $1\le k\le d$, where $k_{(b)}$ is the part of $k$ supported on primes dividing $b$. For $t\ge dA+B$,
```math
b^tF_d(n_jb^{-A})\equiv b^tF_d(n_j)\pmod1.
\tag{7.2}
```
For $0<x_j\le1/2$ and $t\le(d+1)A-E$,
```math
\left|b^t\log(1+x_j)-b^tF_d(x_j)\right|
\le2n_j^{d+1}b^{-E}.
\tag{7.3}
```
Set
```math
P_d=\prod_{\substack{d/2<p\le d\\p\nmid b}}p.
```
For any circle interval $I$, any real $\vartheta$, any integer $t\ge0$, and any consecutive interval $T$ of integer row indices,
```math
\left|\#\lbrace j\in T:\lbrace \vartheta+b^tF_d(n_j)\rbrace \in I\rbrace 
-|T|\,|I|\right|
\le \frac{2|T|}{P_d}+2L_d.
\tag{7.4}
```
The empty product is one. Equations (7.2) and (7.3), followed by interval enlargement by the right side of (7.3), give a finite estimate for the literal logarithmic phases.

**Proof.** Write $k=k_{(b)}k_c$, where $(k_c,b)=1$. Since $\varphi(k_c)\le k\le D$, its value divides $L_D$, so $b^A\equiv1\pmod{k_c}$. Both $b^{t-Ak}$ and $b^t$ vanish modulo $k_{(b)}$, and they agree modulo $k_c$. Their difference is therefore divisible by $k$. Multiplying by $n_j^k/k$ and summing proves (7.2). Taylor's convergent series gives remainder at most $2x_j^{d+1}$; multiplication by $b^t$ gives (7.3).

Write $L_d=P_dQ$. Each prime in $P_d$ occurs to the first power in $L_d$, since $p>d/2$ and $p^2>d$. In the integer polynomial $L_dF_d(z)$ modulo such a $p$, every summand vanishes except $k=p$. Consequently it is a nonzero scalar multiple of $z^p\equiv z\pmod p$. Since $p\nmid b$, the map $j\mapsto n_j$ is a permutation modulo $p$. Conditional on a residue $j\pmod Q$, all the $p$-primary phase coordinates are independent uniform residues by CRT. Their sum is a translated uniform grid of $P_d$ points on the circle. An interval contains $|I|P_d+O(2)$ of those points. Thus (7.4) holds over each complete period of length $L_d$. The at most two incomplete pieces of a consecutive row interval have total length below $2L_d$, proving the stated bound. $\square$

No statement about the digits of $\vartheta$ entered this proof. All denominator parts and the base factors were retained. An irregular row subset would need its own discrepancy estimate modulo $L_d$; (7.4) does not automatically apply to it.

For a word of length $\ell$, use the radix interval of length $b^{-\ell}$. A phase perturbation of size $\eta$ changes membership only within $\eta$ of its two endpoints. Applying (7.4) to those boundary intervals pays an additional $O(\eta |T|+|T|/P_d+L_d)$. This is a word-frequency argument with explicit boundary cost, rather than a claim that approximate real values always share digits.

## Approximation and source count barriers

**BND-001.** Consider any uniform-center whole-prefix construction
```math
X(\theta)=0.\operatorname{pref}_{b,K_1}(\theta+\delta_1)
\operatorname{pref}_{b,K_2}(\theta+\delta_2)\cdots
```
with a schedule independent of $\theta$. If fixed-word discrepancy tends to zero uniformly in $\theta$ through all prefixes, then $K_J/S_J\to0$. Consequently $\log S_J=o(J)$ and $J/\log S_J\to\infty$.

**Proof.** Choose $\theta_J=-\delta_J\pmod1$; the entire $J$-th row consists of zeros. Uniform one-digit convergence at both $S_J$ and $S_{J-1}$ gives
```math
(1-1/b)K_J=o(S_J)+o(S_{J-1})=o(S_J).
```
This proves the first assertion. For $J\ge2$,
```math
\log S_J-\log S_{J-1}=-\log(1-K_J/S_J)\longrightarrow0.
```
Summing these increments and using Cesàro averaging yields $\log S_J=o(J)$. Since $S_J\to\infty$, the last conclusion follows. $\square$

This constrains the number of rows in this particular uniform whole-prefix architecture. It is not a lower bound on the number of distinct sources in all normal-number constructions, and says nothing against a fixed normal number having a short independent definition.

**BND-002.** Suppose $0<\epsilon_j<1$, $\epsilon_j\to0$, and $X$ concatenates the complete $K_j$-digit prefixes of $\epsilon_j$ at center zero. Set $L_j=\max(0,\lceil\log_b(1/\epsilon_j)\rceil-1)$. If the row count is $o(S_J)$ and $X$ is normal, then
```math
\sum_{j\le J}\min(K_j,L_j)=o(S_J).
\tag{7.5}
```

**Proof.** The first $L_j$ source digits are zero. Fix a word length $\ell$. There are at least $\sum_{j\le J}(\min(K_j,L_j)-\ell+1)_+$ starts of $0^\ell$ in these initial zero segments. If the left side of (7.5), divided by $S_J$, has limsup $\rho>0$, these starts have limsup at least $\rho$, because $\ell J=o(S_J)$. Normality gives the limit $b^{-\ell}$. Taking fixed $\ell$ arbitrarily large forces $\rho=0$. $\square$

For the logarithmic schedule, $\epsilon_j\asymp j b^{-A_j}$, so the closeness horizon is $A_j-O(\log j)$, while the copied length is $A_jD_j$. Since $D_j\to\infty$, most copied digits occur after this horizon. Uniform normality of the output is therefore compatible with a completely nonnormal center.

**BND-003.** Let $g$ and $h$ be distinct real analytic germs at zero, with $g(0)=h(0)=0$. Let $x_j=(bj+1)b^{-A_j}\to0$, and suppose $A_j\to\infty$, $\log j=o(A_j)$, and $K_j/A_j\to\infty$. Then $g(x_j)$ and $h(x_j)$ cannot have identical first $K_j$ fractional digits in base $b$ for infinitely many sufficiently large $j$.

**Proof.** Their difference has a first nonzero Taylor term $cx^m$. Hence $|g(x_j)-h(x_j)|\ge c'|x_j|^m$ for large $j$. Identical prefixes give circle distance at most $b^{-K_j}$. Both values tend to zero, so for large $j$ their small real difference equals their circle distance. But
```math
-\log_b(c'|x_j|^m)=mA_j-O(\log j)=O(A_j)=o(K_j),
```
a contradiction. $\square$

Analytic interpolation cannot freely prescribe infinitely many long blocks at these inputs. A proposed representation of a traditional constant must supply the actual Taylor coefficients, their arithmetic constraints, convergence, and the exponentially fine residual bounds.

## Local inverse approximation and arithmetic separation

**CON-009.** Let $g$ be a real $C^1$ function on an interval, with $g'(x_0)\ne0$, and let $\xi=g(x_0)$. On a sufficiently small compact neighborhood of $x_0$, superapproximation
```math
0<|\xi-g(p_n/q_n)|<H(p_n/q_n)^{-M_n},\quad
H\to\infty,\quad M_n\to\infty
```
by reduced rationals of height $H(p/q)=\max(|p|,q)$, with $q>0$, is equivalent to $x_0$ being Liouville. Here all inputs must remain in the regular inverse branch and converge to $x_0$.

**Proof.** Continuity of the derivative and its nonvanishing give constants $0<c<C$ with
```math
c|r-x_0|\le |g(r)-g(x_0)|\le C|r-x_0|
```
on that neighborhood. Since it is bounded, $q\le H(p/q)\le C' q$ for rational inputs in it. The fixed constants are absorbed by decreasing each unbounded approximation exponent by a fixed factor. The positivity of the error excludes $r=x_0$. These observations prove both implications. $\square$

For $g=\log$ on positive inputs, this says that $\xi$ is superapproximable by rational logarithms exactly when $e^\xi$ is Liouville. At a fixed rational $r=a/c>0$, distinct reduced $p/q$ satisfy
```math
|r-p/q|\ge1/(cq).
```
The local lower Lipschitz bound for the logarithm therefore forbids such superapproximation to $\log r$. A construction requiring it cannot identify its output with that prescribed logarithm.

## Classical normal Liouville construction

## Finite normal packets

**CON-002.** For each $j\ge1$, there is an effectively specified cyclic word $W_j$ of length $L_j=b^j$ in which every length-$j$ word appears exactly once cyclically. Every word of length $\ell\le j$ appears $b^{j-\ell}$ times cyclically. In the ordinary, noncyclic word its count differs by at most $\ell-1$.

**Proof.** Form the directed graph whose vertices are words of length $j-1$, including the single empty word when $j=1$. Each word of length $j$ is an edge from its first $j-1$ letters to its last $j-1$ letters. Each vertex has indegree and outdegree $b$. The graph is strongly connected: append the letters of a desired vertex in order. A finite balanced connected directed graph has an Euler circuit. One proof follows unused outgoing edges until a circuit closes, then splices in a new circuit at any visited vertex with unused edges; balance prevents getting stuck elsewhere, and finiteness terminates the process. Choosing starting vertex and edges in lexicographic order makes the construction effective.

Read one letter per traversed edge around the circuit. Each length-$j$ word is one edge, proving the first statement. A fixed length-$\ell$ word has $b^{j-\ell}$ extensions to a length-$j$ word, proving the second. Only the last $\ell-1$ cyclic starts cross the end of the ordinary word. $\square$

These are de Bruijn packets. Their use here is classical and provides an explicit finite source for the following argument; no new priority claim is involved.

**CON-003.** Let $W_j$ be words of lengths $L_j\to\infty$ such that the cyclic frequency of every fixed word in $W_j$ tends to its uniform value. Choose positive repetition counts $R_j$, and set
```math
U_j=\sum_{i<j}R_iL_i,
\qquad Y=0.W_1^{R_1}W_2^{R_2}\cdots.
```
If $L_j/U_j\to0$, then $Y$ is normal through every prefix. The finitely many initial stages with $U_j=0$ are irrelevant.

**Proof.** Fix a length-$\ell$ word. The count in $q$ consecutive copies of $W_j$ differs from its expected value by at most
```math
qL_j\epsilon_j+O(\ell),
```
where $\epsilon_j\to0$ is the cyclic frequency error; this follows by considering the periodic sequence $W_j^\infty$ and deleting its last $\ell-1$ starts. At a prefix inside stage $j$, at most one unfinished copy costs $L_j$ starts. Stage joins contribute at most $\ell$ per stage. Because $L_i\to\infty$ and $R_i\ge1$, the number of stages divided by the total length tends to zero. The weighted sum of $\epsilon_i$ over complete copies is $o(N)$: discard finitely many initial stages, then bound every later $\epsilon_i$ by a common arbitrary tolerance. The unfinished copy contributes at most $L_j/N\le L_j/U_j\to0$. These estimates hold at every prefix $N$, including the first few copies of a new packet. $\square$

**CON-004.** There is an explicitly computable Liouville number normal in base $b$.

**Proof.** Use the packets of CON-002. Having computed their lengths, choose $R_j$ effectively large enough that, with $T_j=U_j+R_jL_j$,
```math
T_j>(j+1)(U_j+L_j),\qquad T_j\ge j L_{j+1}.
```
Then $L_{j+1}/U_{j+1}\le1/j$, so CON-003 gives normality of $Y$. Let $y_j$ be the rational with the first $U_j$ digits of $Y$ and then the packet $W_j$ repeated forever. It has a denominator dividing
```math
Q_j=b^{U_j}(b^{L_j}-1)<b^{U_j+L_j}.
```
Since $Y$ and $y_j$ agree for $T_j$ digits,
```math
|Y-y_j|\le b^{-T_j}<Q_j^{-(j+1)}.
```
Normality implies irrationality: an eventually periodic digit sequence omits some sufficiently long word, since a period of length $P$ has at most $P$ distinct starts of any given length in its tail. Thus the displayed errors are nonzero. Reducing the denominators only strengthens the approximation; the reduced denominators must be unbounded, since otherwise a subsequence of these rational approximants would be constant while converging to the irrational $Y$. Therefore $Y$ is Liouville. $\square$

The factors $b^{L_j}-1$ allow very long repetitions of packets which already have the right finite statistics. Approximants with denominator only $b^n$ instead force long constant runs. This distinction is why an excellent rational approximation need not obstruct normality.

