# Collatz with a density-zero set of changed steps

A single explicit modification of the Collatz rule makes **every positive orbit reach the cycle $`1\leftrightarrow2`$**, while changing the rule on a set of natural density zero. Periodic changes of arbitrarily small positive density can force convergence to that same cycle. Separately, the fraction of classes needed to force uniform descent has a sharp asymptotic order. These answer [Question 7.12 of Oleg Vasilyev's *Up or down at every integer*, arXiv:2611.20344v2](https://arxiv.org/html/2611.20344v2#S7). Neither result proves the ordinary Collatz conjecture.

Take the shortcut map $`T(x)=x/2`$ for even $`x`$ and $`T(x)=(3x+1)/2`$ for odd $`x`$. A removal of an odd point replaces its image by $`D(x)=(x+1)/2`$. Set

```math
\beta=\log_3 2,\qquad H=-\beta\log_2\beta-(1-\beta)\log_2(1-\beta),\qquad \rho=2^H.
```

## Results

**One fixed set of changes.** There is an explicit computable set $`R`$ of odd integers, with $`\#(R\cap[1,X])\asymp X^H/(\log X)^{3/2}`$, such that replacing the up step precisely there makes every orbit reach $`1\leftrightarrow2`$. It has density zero since $`H<1`$. Neither point of the cycle is changed.

**Periodic changes.** Let $`\delta_k`$ be the least fraction of classes modulo $`2^k`$ that must change for uniform descent, and $`\delta_k^{-}`$ the minimum when only odd up steps can be removed. Then

```math
\delta_k\asymp\delta_k^{-}\asymp \frac{2^{-(1-H)k}}{k^{3/2}}.
```

Uniform descent means that some fixed number of steps decreases every sufficiently large input; it does not by itself prescribe a final cycle. [Section 5](#5-arbitrarily-sparse-periodic-changes-that-reach-the-same-cycle) gives periodic refinements that force the target cycle at arbitrarily small positive density.

**A faster variant.** A second explicit set of the same counting order gives convergence in $`O((\log(2+x_0))^2)`$ shortcut steps from $`x_0`$. The bound is for that modified map only.

The periodic lower bound allows changes at even as well as odd classes. The nonperiodic counting bound concerns the specified sets, not all possible nonperiodic modifications.

## 1. One fixed computable set of density zero

Let $`h(x)=\lfloor\log_2 x\rfloor`$ and

```math
W(x)=\min_{0\le j\le h(x)} T^j(x),\qquad
 R=\{x>1:x\ {\mathrm{odd}},\ W(x)=x\}.                                  \qquad (1)
```

The orbit used to define $`W`$ is always the **ordinary** $`T`$ orbit, of bounded length. There is no unbounded stopping-time oracle in this definition. For example, the one-step ordinary window at 3 is 3, 5, so the modified rule sends 3 to 2. Define $`\widetilde T(x)=D(x)`$ at $`x\in R`$, and $`\widetilde T(x)=T(x)`$ elsewhere. In the notation of Question 7.12 the up-set is $`S=(2\mathbb N-1)\setminus R=(2\mathbb N-1)\triangle R`$.

**Global convergence.** The positive integer $`W`$ is nonincreasing along every $`\widetilde T`$ trajectory and strictly decreases at every changed step. If $`x\in R`$, then

```math
W(\widetilde T(x))\le D(x)<x=W(x).
```

At an unchanged odd $`x>1`$, a minimizing literal index $`j`$ is at least one, since $`W(x)<x`$; as $`T(x)>x`$, $`h(T(x))\ge h(x)`$ and $`j-1`$ remains in the new window. At an unchanged even $`x\ge2`$, the immediate halving ensures $`W(x)<x`$ and again $`j\ge1`$; now $`h(T(x))=h(x)-1`$, so $`j-1`$ still remains in the new window. Both cases give $`W(T(x))\le T^{j-1}(T(x))=W(x)`$. Finally $`W(1)=W(2)=1`$ and neither edge of their ordinary cycle is modified.

There can therefore be at most $`W(x_0)-1`$ changed steps along a trajectory. In fact $`W-1`$ at least halves at each change, so the number of changes is $`O(\log(2+x_0))`$. After the last one its literal evolution agrees with $`T`$. From each remaining odd $`x>1`$ the very definition of $`R`$ supplies a strictly smaller actual value within $`h(x)`$ steps, and from each even $`x>1`$ there is an immediate decrease. Successive such actual drops in positive integers terminate at 1. This proves that **every orbit of the one modified map reaches $`(1,2)`$**, with no finite numerical basins assumed.

**Parity words.** In a shell $`2^k\le x<2^{k+1}`$, the first $`k`$ ordinary parity bits run through all binary words exactly once. If two starts have the same first bit, the difference after one step is their difference multiplied by $`1/2`$ or $`3/2`$. Induction shows that matching the first $`k`$ bits is equivalent to congruence modulo $`2^k`$. This is the [Terras parity bijection](https://matwbn.icm.edu.pl/ksiazki/aa/aa30/aa3034.pdf). We use it to count starts by their ordinary parity words.

## 2. Periodic uniform descent, with an explicit set of flipped classes

For fixed $`k\ge1`$ and each residue $`r\bmod2^k`$, define

```math
c(r)=\min_{0\le j\le k}3^{a_j(r)}/2^j,\qquad
 R_k=\{r\bmod2^k:c(r)=1\}.                                         \qquad (3)
```

The $`a_j(r)`$ come from the true ordinary parity prefix of the residue, not from the modified process. Every even residue has $`c(r)\le1/2`$, so only odds are flipped. Flip the up edge to down at residues of $`R_k`$ and preserve all other steps.

Consider its finite residue graph as in [Vasilyev, Section 5.4](https://arxiv.org/html/2611.20344v2), with each edge weighted by its linear multiplier $`f(r)\in\{1/2,3/2\}`$. From an untouched residue, $`c(r)<1`$, so a source prefix attaining $`c(r)`$ has **positive length** $`j\le k`$. At either allowed ordinary successor $`s`$ the first $`j-1`$ ordinary parity bits equal the shifted source prefix (because the successor is determined modulo $`2^{k-1}`$). Thus

```math
f(r)c(s)\le c(r).
```

At a flipped residue $`c(r)=1`$ and $`f(r)=1/2`$, so $`f(r)c(s)\le1/2<c(r)`$. Any graph cycle containing a flipped vertex thus has strictly contracting product.

If a graph cycle has no flipped vertex, its edges are ordinary. The ordinary residue graph is conjugate under the parity bijection to the length-$`k`$ binary shift graph: the two successors shift the known $`k-1`$ bits and append either bit. Hence around the cycle every length-$`k`$ block of the formal periodic ordinary word is the genuine residue's ordinary word. If its total log gain were nonnegative, rotate after a minimum of partial log gains in one period; all partial gains of the infinite repeated word are then nonnegative from that vertex. It would have $`c(r)=1`$ and be flipped, a contradiction. So **all** cycles have strictly negative log gain. Finite graph cycle decomposition gives a fixed path length with uniformly contracting coefficient (or apply Vasilyev's equivalent criterion). This proves periodic uniform descent. It does not assert that the bounded integer orbits of every one of these specific periodic variants reach $`(1,2)`$.

**A lower bound allowing arbitrary changes, not just removals.** Let $`m=\lfloor\beta k\rfloor+1`$. Each distinct cyclic rotation orbit of weight-$`m`$ binary words of length $`k`$ gives a directed simple ordinary cycle under the parity conjugacy, of period dividing $`k`$ and positive log gain. Different rotation orbits use disjoint vertices, even when a word has proper period. There are at least $`\binom{k}{m}/k`$ such cycles. A uniformly descending periodic modification must change some vertex in each cycle, since otherwise all its original edges and weights remain. Thus the minimum number of changed classes is $`\gg \rho^k/k^{3/2}`$ by Stirling. This also shows precisely why a set consisting only of a subexponential number of short periodic parity shadows cannot serve as a uniform vertex-deletion certificate at arbitrarily deep dyadic conductors.

## 3. Counting the exceptional words

Let $`B_n`$ count binary words of length $`n`$ for which every nonempty prefix has strictly positive sum of increments $`b-\beta`$, and let $`U_n`$ count words with strictly positive terminal sum. Irrationality of $`\beta`$ makes weak and strict inequalities equivalent at positive lengths. Then $`B_k=\#R_k`$ in (3). Stirling and geometric binomial-tail comparison give $`U_n\ll \rho^n/\sqrt{n}`$, since the boundary quota is $`\lfloor\beta n\rfloor+1`$ and the ratio of successive tail terms is bounded by a fixed number less than one for large $`n`$. We use the exact formal identity

```math
\sum_{n\ge0} B_n z^n
                 =\exp\!\left(\sum_{n\ge1} \frac{U_n}{n}z^n\right).  \qquad (4)
```

This is the strictly-positive Sparre Andersen identity; the following finite labelled argument makes the convention and hypotheses explicit.

For a fixed labelled list of increments, perturb its entries sufficiently little and generically so the signs of all subset sums are unchanged and distinct disjoint nonempty subsets have different averages. This is possible because of irrational $`\beta`$, finite subsets, and finitely many equal-average hyperplanes. In each cycle of a permutation of the labels, rotate the cyclic word so its partial sums lie above its chord: subtract its mean and start after the unique minimum centered partial sum among time positions before the end. Concatenate the blocks in order of increasing mean. The straight chords are precisely the lower convex minorant of the path: they form a convex interpolation lying below every path point, and any convex minorant must lie below each chord by its endpoints. Conversely, the faces of the lower convex minorant of any ordering yield its blocks and the original cycles; their slopes are distinct and all interior points strictly above their face chord by genericity. All partial sums of the ordering are positive exactly when all block sums are positive: the first face slope is the minimum of the prefix averages, and later slopes increase. Hence the number of permutations with all cycle sums positive equals the number of orderings with all positive partial sums. The perturbations have not changed either sign condition for the original list.

Average this equality over independent fair binary increments. For a fixed permutation with $`m_j`$ cycles of length $`j`$, disjoint cycles have independent positive-sum events with probabilities $`U_j/2^j`$. There are $`n!/\prod_j(j^{m_j}m_j!)`$ permutations of this cycle type. Divide by $`n!`$, multiply by $`2^n`$, and sum over the types. This gives (4).

Normalize $`z\mapsto z/\rho`$ in (4). The coefficients of the exponent are bounded by $`C(n+1)^{-3/2}`$, and the sequence $`b_n=(n+1)^{-3/2}`$ satisfies $`(b*b)_n\le C' b_n`$ by splitting at $`n/2`$. The $`m`$-fold convolution of the exponent's coefficients is therefore at most $`C^m(C')^{m-1} b_n`$ for $`m\ge1`$. Summing with the factors $`1/m!`$ proves $`B_n\ll \rho^n/(n+1)^{3/2}`$. The lower necklace bound gives the other inequality. Together, the explicit upper bound and the expanding necklace lower bound give the stated sharp order for both periodic minima.

## 4. A faster rule, and the size of both exceptional sets

The same construction can guarantee efficient convergence if the change test asks for a **fixed fractional** rather than strict local drop. With $`W`$ as in (1), let

```math
R_{\mathrm{frac}}=\{x>1:x\ {\mathrm{odd}},\ W(x)>3x/4\},
```

and again replace up by the down step there only.

At an unchanged state above 1, the window-shift argument of Section 1 makes $`W`$ nonincreasing. At a changed odd $`x\ge3`$, $`D(x)\le2x/3<(8/9)W(x)`$.

Start a phase at $`x\le x_0`$. Try to follow the ordinary window to its minimum $`v=W(x)`$. An interrupting change drops the potential below $`8/9`$ of its phase-start value and outputs a state at most $`x_0`$. Otherwise reach $`v`$, and, if not yet in the cycle, try a second ordinary window from $`v`$. A change again drops the potential by the stated factor. Without a change, an untouched odd $`v`$ has a witness at most $`3v/4`$, and an even $`v`$ can halve immediately. The new potential in this case is at most $`3/4`$ of the old one. Thus every nonterminal phase decreases the potential by a fixed factor, restarts at a state at most $`x_0`$, and takes at most $`2\lfloor\log_2 x_0\rfloor`$ steps. There are $`O(\log(2+x_0))`$ phases, giving **$`O((\log(2+x_0))^2)`$ actual shortcut steps**. Intermediate values have $`O(\log(2+x_0))`$ bits by the all-up bound over a phase, so the literal look-ahead costs polynomial bit time as well.

**Sharp counts for both rules.** In a shell $`2^k\le x<2^{k+1}`$, membership in $`R_{\mathrm{frac}}`$ means that the entire ordinary window stays above $`3x/4`$. For any prefix of length $`j\le k`$, the difference between its true log gain and its coefficient log gain is a sum of terms $`\ln(1+1/(3T^i(x)))`$ over odd inputs. Because those inputs exceed $`3x/4`$, the sum is at most $`4k/(9x)<1`$. Hence every partial coefficient log exceeds $`\ln(3/4)-1`$. Prepend a fixed number $`m`$ of ones with total log gain greater than $`1-\ln(3/4)`$. This injects those parity words into the positive-prefix words counted by $`B_{k+m}`$.

Conversely, the $`B_k`$ positive-prefix words all belong to $`R`$: the ordinary affine corrections are nonnegative and every prefix coefficient is at least one. Therefore the shell counts satisfy

```math
B_k \le \#(R\cap[2^k,2^{k+1})) \le \#(R_{\mathrm{frac}}\cap[2^k,2^{k+1})) \le B_{k+m}.
```

The bounds for $`B_k`$ give the claimed counting order for both sets. Use the last completed shell for the lower bound and sum a geometrically dominated series through the current shell for the upper bound. This proof needs no bound on linear forms in logarithms.

## 5. Arbitrarily sparse periodic changes that reach the same cycle

**Theorem.** For each $`\varepsilon>0`$, there is a set of odd classes modulo some power of two, of density less than $`\varepsilon`$, whose removal from the up steps gives uniform descent and makes every positive orbit reach $`1\leftrightarrow2`$.

Choose a base map $`F_0`$ from Section 2 with period $`Q=2^k`$, $`k\ge2`$, and change density below $`\varepsilon/2`$. It preserves the target cycle: the first two ordinary multipliers from 1 have product $`3/4`$, so 1 is not flipped. There are effective constants $`L,A`$ and $`0<\theta<1`$ such that every length-$`L`$ base residue path has multiplier at most $`\theta`$ and affine intercept at most $`A`$. Choose an integer $`B\ge2`$ with $`B>A/(1-\theta)`$. The bound $`F_0^L(x)\le\theta x+A`$ forces every base orbit into $`[1,B]`$. Iteration and a bound for the last, incomplete block give $`F_0^j(x)\le C_1\theta^{\lfloor j/L\rfloor}x+C_2`$, for some constants $`C_1,C_2`$.

Choose $`J`$ so that $`C_1\theta^{\lfloor(J-1)/L\rfloor}\le1/(4B)`$. Refine to a dyadic period $`M`$ divisible by $`Q`$ and $`2^J`$ with

```math
M>2B,\qquad M>4BC_2,\qquad M/2^J>(3/2)^J(B+1),\qquad B/M<\varepsilon/2.
```

Keep the base changes. Also remove the up step at each residue modulo $`M`$ whose representative $`r`$ is an odd, still-up point in $`[3,B]`$. This costs at most $`B/M`$ in density. Now every point in $`[3,B]`$ goes down and the target cycle survives.

**The orbit enters the interval.** Suppose it always stays above $`B`$. Consider consecutive visits to extra classes $`x=r+tM`$ and $`x'=r'+t'M`$, with $`t,t'\ge1`$, separated by $`j`$ steps. If $`j\le J`$, replay the same affine formulas from $`r`$. This is initially justified only by parity: after $`i`$ steps the discrepancy is $`3^{a_i}tM/2^i`$, where $`a_i`$ is the up count. The replay endpoint $`y`$ is positive and below $`M/2^J`$, as seen by bounding all steps by the all-up map. Since $`y\equiv r'\pmod{M/2^j}`$ and $`r'\le B<M/2^J`$, it follows that $`y=r'`$. Now $`t'=3^{a_j}t/2^j`$ is an integer, so $`2^j`$ divides $`t`$. This restores congruence modulo the full period $`M`$ throughout the replay, so the replay was an orbit of the refined map. On $`[1,B]`$ it decreases until entering the target cycle, so $`r'<r`$. Nonnegative affine intercept then gives multiplier $`3^{a_j}/2^j<1`$ and $`t'<t`$.

If $`j>J`$, the first step is down and the next $`j-1`$ steps follow $`F_0`$. Hence $`x'\le x/(4B)+C_2\le x/(2B)<tM`$, again giving $`t'<t`$. There cannot be infinitely many such visits. After the last, or if there are none, the orbit follows $`F_0`$ and enters $`[1,B]`$. All orbits therefore reach the cycle.

**Uniform descent survives.** Every finite symbolic residue path has arbitrarily large integer lifts: at each step, the next free binary bit of the start selects either successor, since each affine numerator has odd slope. More explicitly, starts for an $`i`$-edge prefix are a class modulo $`2^iM`$, and their images at time $`i`$ differ by an odd multiple of $`M`$ times the free integer parameter; its parity selects the next successor. Thus the short extra-to-extra replay also bounds symbolic segment multipliers strictly below one. Long segments have multiplier at most $`1/(4B)`$ by the long-segment bound on arbitrarily large lifts. Every cycle with extra events splits into contracting segments, while a cycle without events projects to a nonempty closed walk of the base graph. The cycle criterion of Section 2 gives uniform descent.

This refinement makes the final cycle the same for every orbit; it does not give the sharp rate from Section 3 in terms of the refined period. Nonempty periodic sets have positive density, so this theorem gives arbitrarily small density, not exactly zero.

## What this says about ordinary Collatz

An ordinary trajectory must either reach the cycle or hit $`R`$: it agrees with the convergent modified trajectory until its first visit to $`R`$. That visit can occur at the starting point itself. The proof uses the changed down step there. It gives no proof of ordinary convergence, including on Mersenne starts.

## Reproducibility and credit

Run [the exact finite checker](check-density-zero.js) with Node.js:

```sh
node check-density-zero.js
```

The checker covers the positive-prefix recurrence through length 256, all 131,070 residues across the first 16 dyadic moduli, 262,140 weighted edge inequalities, and 32,768 starts for each nonperiodic rule. These finite checks illustrate the construction; the proofs above do not rely on them.

This writeup is by Mira Cult. OpenAI models assisted with the proof, exposition and checking under Mira's guidance. Separate nonauthor automated proof checks covered the original answers, the sharp estimates, the periodic refinement, and the improved step bound. This is not a formalization or an external referee report. No historical priority claim is made.
