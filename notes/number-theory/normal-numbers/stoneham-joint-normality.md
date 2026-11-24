# Joint normality for Stoneham series

**Mira Cult**

Stoneham's construction gives explicit normal numbers. The same approach also controls the digits of several related series **jointly**, in a common base. In particular, a nontrivial rational linear combination of the series below is normal in that base. The proof tracks which prime powers survive in the denominators of the partial sums.

## Statements

A number $`x`$ is **normal in base $`b`$** if every word of length $`k`$ in its base-$`b`$ expansion has limiting frequency $`b^{-k}`$, counting overlapping starts. Equivalently, the fractional parts of $`b^n x`$ are uniformly distributed in $`[0,1)`$.

**Theorem 1 (joint normality).** Fix an integer $`b\ge2`$. For every prime $`p\nmid b`$ and positive integer $`s`$, put

```math
L_{p,s}(b)=\sum_{j=0}^{\infty}\frac{1}{p^{sj}b^{p^j}}.
```

For every finite list of distinct pairs $`(p_i,s_i)`$, the vectors $`(\{b^nL_{p_i,s_i}(b)\})_i`$ are uniformly distributed in the corresponding unit cube as $`n\to\infty`$. Consequently, every rational linear combination with at least one nonzero coefficient is base-$`b`$ normal, with or without a rational constant term.

The classical Stoneham number $`\alpha_{b,p}=\sum_{j\ge1}p^{-j}b^{-p^j}`$ is $`L_{p,1}(b)-1/b`$. Thus, for example, $`\alpha_{2,3}-(2/5)\alpha_{2,5}`$ is binary-normal. The theorem also allows several values with the **same** prime and different $`s`$. For $`s=1`$, the values are real logarithms of the Artin–Hasse exponential at $`1/b`$.

**Theorem 2 (series supported on finitely many primes).** Let $`S`$ be a fixed nonempty finite set of primes, none dividing $`b`$. If $`\mathcal M(S)`$ is the set of positive integers all of whose prime divisors belong to $`S`$ (including $`1`$), then for every positive integer $`s`$ the number

```math
\Theta_{b,S,s}=\sum_{m\in\mathcal M(S)}\frac{1}{m^s b^m}
```

is base-$`b`$ normal. For instance, the series supported on integers $`3^i7^j`$ with weights $`(3^i7^j)^{-1}`$, at base $`10`$, is decimal-normal.

**Theorem 3 (separate position and denominator parameters).** For integers $`B,C,D\ge2`$, the series

```math
S_{B,C,D}=\sum_{j\ge1}\frac{1}{D^jB^{C^j}}
```

is base-$`B`$ normal if and only if $`D`$ has a prime divisor not dividing $`B`$. If no such prime exists, the nonzero digits have density zero in base $`B`$.

## A power-orbit estimate

Write $`e(t)=\exp(2\pi i t)`$. Fix $`b`$ and a finite prime set $`S`$ coprime to $`b`$. Fix $`0\lt \epsilon\lt A`$. For all sufficiently large integers $`q`$ supported on $`S`$, all $`a`$ coprime to $`q`$ and all lengths $`q^\epsilon\le L\le q^A`$, there is a $`\delta\gt 0`$ independent of $`a,q,L`$ such that

```math
\left|\sum_{j=0}^{L-1}e\!\left(\frac{ab^j}{q}\right)\right|
\ll Lq^{-\delta}.
```

The estimate is uniform in the starting exponent: its power of $`b`$ can be incorporated in $`a`$. A fixed nonzero integer multiplier in the phase is harmless, since reducing the fraction changes $`q`$ by at most a fixed factor; one may slightly widen the allowed powers of $`q`$.

To prove the estimate, write $`q=\prod_{p\in S}p^{e_p}`$ and choose an integer $`d\ge2`$ with $`d\epsilon\gt 1`$. Set

```math
t_0=2\mathrm{lcm}_{p\in S}(p-1),\qquad
t=t_0\prod_{p\in S}p^{\lceil e_p/(d+1)\rceil},\qquad U=b^t-1.
```

The lifting-the-exponent formula gives $`v_p(U)=v_p(b^{t_0}-1)+\lceil e_p/(d+1)\rceil`$. For $`p=2`$ this uses $`b^{t_0}\equiv1\pmod4`$. Thus $`q\mid U^{d+1}`$ and $`t\asymp q^{1/(d+1)}`$. On the progression $`j=r+t\ell`$, the phase modulo integers is the polynomial

```math
P_r(\ell)=\frac{ab^r}{q}\sum_{i=0}^{d}\binom{\ell}{i}U^i .
```

Its leading coefficient has reduced denominator $`q_*\asymp q^{1/(d+1)}`$: for $`p\in S`$ its exponent differs from $`e_p/(d+1)`$ by $`O(1)`$, by the valuation of $`ab^rU^d/(d!q)`$; primes outside $`S`$ contribute only a divisor of $`d!`$. Every progression has length $`K\asymp L/t`$. The [classical Weyl inequality](https://www.math.purdue.edu/~twooley/2023ant/2023antnotes.pdf), Lemma 3.7, bounds its exponential sum by

```math
\ll_{d,\rho} K^{1+\rho}
\left(q_*^{-1}+K^{-1}+q_*K^{-d}\right)^{1/2^{d-1}} .
```

Each term in parentheses saves a fixed power of $`q`$: the last is $`O(q^{1-d\epsilon})`$, and the other two save because $`d\epsilon\gt 1`$. Take $`\rho\gt 0`$ small enough relative to $`A`$ and sum the progression estimates. All constants can depend on the fixed prime set; no uniformity as that set grows is asserted.

## From partial sums to actual digits

We use the following reduction in the three proofs. On each dyadic digit interval $`[X,2X)`$, suppose that, apart from $`o(X)`$ exceptional positions, the orbit of a real $`x`$ is approximated with a uniform $`o(1)`$ error modulo one by consecutive power orbits of rational numbers. Suppose there are $`O((\log X)^r)`$ such pieces for a fixed $`r`$, and the reduced denominators share a fixed prime support coprime to the base and lie between $`cX^\alpha`$ and $`CX^\beta`$ for fixed $`0\lt \alpha\le\beta`$. Here each piece begins with a reduced rational and proceeds by multiplication by the base.

Intersect with any prefix of the dyadic interval and discard pieces shorter than $`X/(\log X)^{r+2}`$; their combined length is $`O(X/(\log X)^2)`$. On all longer pieces the power-orbit estimate applies with small fixed $`\epsilon\gt 0`$ and large fixed $`A`$. The error in a fixed Weyl sum is $`o(X)`$ because $`e(ht)`$ is Lipschitz for fixed integer $`h`$. The sum of the retained rational estimates is also $`o(X)`$ because their denominators grow by a fixed power of $`X`$. Summing over dyadic intervals gives $`\sum_{n\lt N}e(hb^n x)=o(N)`$ at every endpoint $`N`$ for each $`h\ne0`$.

### Proof of Theorem 1

By the multidimensional Weyl criterion, consider any nonzero integer coefficient vector $`(c_{p,s})`$. Truncate each series of $`x=\sum_{p,s}c_{p,s}L_{p,s}(b)`$ at positions $`p^j\le n`$ and multiply the truncated value by $`b^n`$. For each active prime $`p`$, let $`s_p`$ be the largest $`s`$ with $`c_{p,s}\ne0`$ and put $`k=\lfloor\log_p n\rfloor`$.

For sufficiently large $`n`$ the term with indices $`(p,s_p,k)`$ is the unique term of minimum $`p`$-adic valuation. Terms with smaller $`j`$ in the same column have larger valuation; terms with $`s\lt s_p`$ lose an amount growing linearly in $`k`$; terms for other primes have nonnegative valuation. In particular, neither signs nor carries can cancel this denominator. The reduced denominator of the scaled partial sum has exact $`p`$-exponent $`s_p k-v_p(c_{p,s_p})`$ and is therefore comparable to $`n^{\sum_p s_p}`$.

The partial sums change at $`O(\log X)`$ positions on $`[X,2X)`$ and give an exact rational power orbit between changes. The omitted terms after multiplying by $`b^n`$ have absolute sum $`O(X^{-1})`$: each omitted position $`m\gt n`$ has coefficient bounded in magnitude by a fixed multiple of $`1/m`$ and the factors $`b^{n-m}`$ sum geometrically. The reduction proves Weyl cancellation for every integer coefficient vector, hence joint uniform distribution. Clearing denominators and using [rational affine invariance of normality](https://www.davidhbailey.com/dhbpapers/nonnormality.pdf) gives the rational conclusion (a negative multiplier also preserves uniform distribution by reflection).

### Proof of Theorem 2

Let $`p_0=\min S`$ and let $`k=\lfloor\log_{p_0}n\rfloor`$. Among $`m\in\mathcal M(S)`$ with $`m\le n`$, the only one divisible by $`p_0^k`$ is $`p_0^k`$ itself: a second one would be at least $`p_0^{k+1}\gt n`$. So the term at $`p_0^k`$ in the partial sum scaled by $`b^n`$ forces a denominator divisible by $`p_0^{sk}`$. The denominator divides $`\prod_{p\in S}p^{s\lfloor\log_p n\rfloor}`$. These bounds give the required polynomial lower and upper bounds, respectively.

There are $`O((\log X)^{|S|})`$ changes, by counting the possible prime exponent vectors, and the scaled tail is $`O(X^{-s})`$ by summing over all integer positions greater than $`n`$. The same reduction applies.

### Proof of Theorem 3

Write $`D=D_\parallel Q`$, where every prime of $`D_\parallel`$ divides $`B`$ and $`\gcd(Q,B)=1`$. Choose a fixed integer $`t\ge0`$ such that $`D_\parallel\mid B^t`$ and set $`V=B^t/D_\parallel`$. Then the $`j`$th term is $`V^j/(Q^j B^{C^j+tj})`$.

If $`Q\gt 1`$, the partial sum through $`j`$ has denominator $`Q^j B^{C^j+tj}`$ before reduction, with numerator coprime to $`Q`$: its last summand in the numerator is $`V^j`$ and every earlier one is divisible by $`Q`$. On $`C^j+tj\le n\lt C^{j+1}`$ this gives a rational power orbit with reduced denominator $`Q^j`$. The tail scaled by $`B^n`$ is $`O(D^{-j})`$ by the geometric series bound and the fact that successive positions $`C^i`$ are at least one apart. The skipped ranges $`C^j\le n\lt C^j+tj`$ contain $`O((\log X)^2)`$ positions up to $`2X`$. The denominator is comparable to $`X^{\log_C Q}`$ on the retained ranges intersecting $`[X,2X)`$. The reduction proves normality.

If $`Q=1`$, the $`j`$th term is a terminating base-$`B`$ fraction with at most $`O(j+1)`$ digits supported in a window ending at $`C^j+tj`$. These windows are eventually disjoint, and they eventually start after the end of the finite initial sum. Thus the tail windows cannot create carries between windows or into that initial sum. At most $`O((\log X)^2)`$ positions through digit $`X`$ contain a nonzero digit. This proves the other direction.

## Scope and references

- **Common argument.** With $`F_p(z)=\sum_{j\ge0}p^{-j}z^{p^j}`$ one has $`F_p(z)-p^{-1}F_p(z^p)=z`$. At $`z=1/b`$ and $`p\nmid b`$, the values on the left are individually base-$`b`$ normal (the second is normal in base $`b^p`$), yet the difference displayed is rational. The common argument in Theorem 1 cannot be dropped.
- **No nonlinear or absolute normality claim.** Theorem 1 controls linear projections of the joint radix orbit. It does not give the digit distribution of $`P(L_{p,s}(b))`$ for a nonlinear polynomial $`P`$, for instance the square of a Stoneham number. None of the statements extends automatically to bases multiplicatively independent of the one shown. Nor can one let the prime set in Theorem 2 grow and conclude that its limit is normal.
- [Bailey and Crandall, *Random Generators and Normal Numbers*](https://www.davidhbailey.com/dhbpapers/bcnormal.pdf) treat the classical coprime Stoneham family and more general series. [Bailey and Borwein, *Nonnormality of Stoneham constants*](https://www.davidhbailey.com/dhbpapers/nonnormality.pdf), discuss sum normality and the distinction between defining-base normality and other bases. [Captain Sude's two-sum proof](https://github.com/CaptainSude/Stoneham-sum-normal/blob/main/paper/stoneham-two-sum-normality.tex) treats arbitrary admissible pairs with a common defining base, including shared-prime parameters. That range is different from the joint family here.
- This note consolidates the conventional arguments in [the earlier research archive, S07 and S09](https://gist.github.com/Mira-acc/ea2791119de611279237096e35cbc976). It makes no historical priority claim and is not a formal verification. OpenAI models assisted with the original derivations and the preparation and checking of this exposition under Mira's guidance.
