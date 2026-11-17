# Preserving both prescribed endpoints in a subexponential CRT cover

Mira Cult · 16 November 2026

## Status and scope

This note proves an unconditional covering statement. It does **not** prove that the two surviving forms are simultaneously prime. Its purpose is to remove the previously identified exponential-modulus obstacle from an Erdős–Rankin-style approach to an arbitrary prescribed even gap. The construction works for every sufficiently large even gap, including gaps having a prime factor larger than the covering primes. The literature comparison below identifies an improved quantitative baseline for reduced residues; historical priority remains unestablished.

The analytic inputs are the ordinary prime number theorem, Mertens' product theorem, and the unconditional Brun–Titchmarsh inequality. No zero-free-region claim, distribution conjecture, prime-pair conjecture, or unreviewed quasi-RH input enters this covering theorem.

All logarithms are natural. Write $`\log_2 x=\log\log x`$ and $`\log_3 x=\log\log\log x`$.

## The covering theorem

**Theorem C-SUB.** For every sufficiently large positive even integer $`g`$, put

```math
D=g+1,\qquad
y=8D\frac{\log_3 D}{\log_2 D},\qquad
M=\prod_{p\le y}p.
```

There is an integer $`a`$, with $`1\le a\le M`$, such that

```math
\gcd(a(a+g),M)=1,
\qquad\text{(C1)}
```

and

```math
\gcd(a+j,M)\gt 1\qquad(1\le j\lt g).
\qquad\text{(C2)}
```

Moreover,

```math
\log M=(8+o(1))g\frac{\log_3 g}{\log_2 g}=o(g),
\qquad\text{(C3)}
```

where the assertion is uniform over all sufficiently large even $`g`$. In particular, if $`n\equiv a\pmod M`$ and $`n\gt y`$, every integer strictly between $`n`$ and $`n+g`$ is composite. The two linear forms

```math
L_1(t)=Mt+a,\qquad L_2(t)=Mt+a+g
\qquad\text{(C4)}
```

are admissible.

The constant 8 is deliberately loose. The proof establishes a sufficiently-large threshold but does not calculate a numerical threshold or an executable finite bridge to it. Because the theorem is only a covering statement, calculating that threshold would not establish the prime-gap target.

### Proof

We first construct residue classes $`b_p\pmod p`$, one for every prime $`p\le y`$, which cover precisely all the points of $`[1,D]\cap\mathbb Z`$ except the protected set

```math
H=\{1,D\}.
```

Here and below, “cover” means that $`h\equiv b_p\pmod p`$ for at least one chosen prime $`p`$. Thus every chosen class must avoid both protected endpoints.

Set

```math
L=\log D,\quad L_2=\log L,\quad L_3=\log L_2,
\quad u=L/L_2^2,\quad v=8D/L_2,
\quad y=vL_3.
\qquad\text{(C5)}
```

For all sufficiently large $`D`$,

```math
3\lt u\lt v\lt y\lt D,\qquad uv\gt D,\qquad v^2\gt D,
\qquad R:=D/v=L_2/8\lt u.
\qquad\text{(C6)}
```

All uses of “sufficiently large” in the proof concern these displayed inequalities or classical estimates with an absolute error term; none depends on the factorization of $`D`$.

#### 1. First-stage residue classes

Since $`D`$ is odd, set $`b_2=0`$. Choose any $`b_3`$ avoiding $`1,D\pmod3`$. For every prime $`5\le p\le u`$, choose any residue satisfying

```math
b_p\not\equiv0,1,D\pmod p.
\qquad\text{(C7)}
```

There is always such a residue: at most three residue classes are forbidden and $`p\ge5`$. The exclusion of zero is essential for the later prime-counting calculation.

For each prime $`u\lt p\le v`$ with $`p\nmid D`$, set $`b_p=0`$. This class avoids both endpoints. Leave the primes $`u\lt p\le v`$ dividing $`D`$ unused at this stage, and also leave all primes in $`(v,y]`$ unused. Let $`S`$ be the subset of $`[1,D]\cap\mathbb Z`$ not covered in this first stage. By construction $`H\subset S`$.

#### 2. Classification of survivors

Every $`h\in S`$ belongs to at least one of the following two classes.

**Class I.** Every prime factor of $`h`$ belongs to

```math
\{p:p\le u\}\cup\{p:p\mid D,\ p\gt u\}.
  \qquad\text{(C8)}
```

**Class II.** $`h=mq`$, where $`q\gt v`$ is prime and $`m\le R`$.

Indeed, if $`h`$ has no prime factor exceeding $`v`$, any prime factor $`p\in(u,v]`$ must divide $`D`$, since otherwise the class $`b_p=0`$ would cover $`h`$. This gives Class I. If $`h`$ has a prime factor $`q\gt v`$, it has exactly one such factor, with exponent one, because $`v^2\gt D`$; writing $`h=mq`$ gives $`m\lt D/v=R\lt u`$. Allowing $`m\le R`$ only enlarges the class.

No smoothness assumption on $`g`$, $`D`$, or their prime factors has been made. Allowing the exceptional primes dividing $`D`$ in Class I is the step that protects the arbitrarily prescribed right endpoint.

#### 3. Class I is negligible

The elementary Rankin bound with exponent $`1/2`$ gives

```math
N_I\le D^{1/2}
\prod_{p\le u}(1-p^{-1/2})^{-1}
\prod_{\substack{p\mid D\\p\gt u}}(1-p^{-1/2})^{-1}.
\qquad\text{(C9)}
```

For clarity, this follows by replacing the indicator $`h\le D`$ by $`(D/h)^{1/2}`$ and summing the resulting nonnegative geometric series over all integers whose prime factors lie in (C8). Counting extra integers only increases the upper bound.

Using $`-\log(1-z)\ll z`$ for $`0\le z\le2^{-1/2}`$, and even bounding the first sum over primes by the sum over all integers, the logarithm of the first Euler product is $`O(\sqrt u)`$. The number of distinct primes $`p\gt u`$ dividing $`D`$ is at most $`L/\log u`$, so the logarithm of the second product is

```math
O\left(\frac{L}{\sqrt u\log u}\right).
```

Their sum is $`O(\sqrt L)`$, hence $`o(L)`$, uniformly in $`D`$. Consequently

```math
N_I\le D^{1/2+o(1)}
=o\left(\frac{D L_3}{L L_2}\right).
\qquad\text{(C10)}
```

This avoids a specialized uniform smooth-number theorem.

#### 4. Counting Class II using Brun–Titchmarsh

Put

```math
W=\prod_{5\le p\le u}p,\qquad
A(u)=\prod_{5\le p\le u}\frac{p-2}{p-1},\qquad
F(m)=\prod_{\substack{p\mid m\\p\ge5}}\frac{p-1}{p-2}.
\qquad\text{(C11)}
```

Fix $`m\le R`$. A prime $`q\gt v`$ is coprime to $`W`$. For a prime $`5\le p\le u`$:

* if $`p\mid m`$, then $`mq\equiv0\pmod p`$, so the nonzero condition in (C7) means that $`mq`$ automatically avoids $`b_p`$;
* if $`p\nmid m`$, the condition $`mq\not\equiv b_p\pmod p`$ excludes exactly one of the $`p-1`$ nonzero residue classes for $`q`$.

Since $`m\lt u`$, every prime factor of $`m`$ occurs within the small-prime range. The Chinese remainder theorem therefore shows that the number of permitted reduced residue classes for $`q\pmod W`$ is exactly

```math
\phi(W) A(u)F(m).
\qquad\text{(C12)}
```

Discarding the conditions at 2 and 3, and any other restrictions, only enlarges the count.

The Brun–Titchmarsh inequality states that for $`(c,W)=1`$ and $`t\gt W`$,

```math
\pi(t;W,c)\le\frac{2t}{\phi(W)\log(t/W)}.
\qquad\text{(C13)}
```

This is the initial-segment consequence of Montgomery–Vaughan, *The large sieve*, Mathematika **20** (1973), Theorem 2, equation (1.10). Its hypotheses are unconditional and include arbitrary moduli; no exceptional character has been discarded.

Since $`\log W=O(u)=o(L)`$ and $`t=D/m\ge v`$, we have uniformly over $`m\le R`$,

```math
\log(t/W)\ge\log(v/W)=(1+o(1))L.
```

Applying (C13) separately to the classes in (C12) gives

```math
\#\{q\le D/m:q\text{ is a Class-II survivor prime for this }m\}
\le (2+o(1))\frac{D}{mL}A(u)F(m).
\qquad\text{(C14)}
```

Here the left side may be enlarged to include primes $`q\le v`$; the reduced residue classes used on the right still provide a valid upper bound for the intended primes $`q\gt v`$.

For $`p\ge5`$,

```math
\frac{p-2}{p-1}
=\left(1-\frac1p\right)
\left(1-\frac1{(p-1)^2}\right)
\le1-\frac1p.
```

Mertens' product theorem thus gives

```math
A(u)\le3\prod_{p\le u}\left(1-\frac1p\right)
=\frac{3e^{-\gamma}+o(1)}{\log u}.
\qquad\text{(C15)}
```

To average the correction $`F(m)`$, write

```math
F(m)=\sum_{d\mid m}c(d),
```

where $`c`$ is nonnegative, supported on squarefree integers with prime factors at least 5, and $`c(p)=1/(p-2)`$. Interchanging nonnegative sums and using the harmonic-sum bound gives

```math
\begin{aligned}
\sum_{m\le R}\frac{F(m)}m
&=\sum_{d\le R}\frac{c(d)}d\sum_{k\le R/d}\frac1k\\
&\le(1+\log R)\prod_{p\ge5}\left(1+\frac1{p(p-2)}\right)\\
&=:C_F(1+\log R).
\end{aligned}
\qquad\text{(C16)}
```

The product converges and has the explicit elementary bound

```math
\log C_F
\le\sum_{p\ge5}\frac1{p(p-2)}
\le\sum_{\substack{n\ge5\\n\text{ odd}}}\frac1{n(n-2)}
=\frac16.
\qquad\text{(C17)}
```

We can avoid a loss in the constant by combining the two Euler products exactly. For every prime $`p\ge5`$,

```math
\frac{p-2}{p-1}\left(1+\frac1{p(p-2)}\right)=1-\frac1p.
```

Consequently

```math
\begin{aligned}
A(u)C_F
&=\prod_{5\le p\le u}\left(1-\frac1p\right)
  \prod_{p\gt u}\left(1+\frac1{p(p-2)}\right)\\
&=3\prod_{p\le u}\left(1-\frac1p\right)(1+O(1/u))\\
&=\frac{3e^{-\gamma}+o(1)}{\log u}.
\end{aligned}
\qquad\text{(C17a)}
```

The tail estimate follows by bounding the logarithm of its product by a constant times $`\sum_{n\gt u}n^{-2}`$. Because $`\log u=L_2-2L_3\sim L_2`$ and $`\log R=L_3-\log8\sim L_3`$, summing (C14) and using (C16) and (C17a) yields

```math
N_{II}\le
\left(6e^{-\gamma}+o(1)\right)
\frac{D L_3}{L L_2}
\lt  (6+o(1))\frac{D L_3}{L L_2}.
\qquad\text{(C18)}
```

The second, deliberately weaker numerical inequality needs only $`\gamma\gt 0`$, not a numerical approximation to Euler's constant. All error terms are uniform in the integer $`D`$.

#### 5. Greedy cleanup preserving both endpoints

By the ordinary prime number theorem,

```math
\begin{aligned}
\#\{p:v\lt p\le y\}
&=\pi(y)-\pi(v)\\
&=(8+o(1))\frac{D L_3}{L L_2}.
\end{aligned}
\qquad\text{(C19)}
```

Indeed, $`y=8DL_3/L_2`$, $`\log y\sim L`$, and $`v=y/L_3`$, so $`\pi(v)=o(\pi(y))`$. By (C10) and (C18), the number in (C19) exceeds $`|S|+2`$ for all sufficiently large $`D`$.

Take an interior survivor $`h\in S\setminus H`$. There are at most two primes $`p\gt v`$ dividing $`(h-1)(h-D)`$: each of the two nonzero factors has absolute value less than $`D\lt v^2`$, and hence has at most one prime divisor greater than $`v`$. Choose an unused prime $`p\in(v,y]`$ dividing neither factor, and set

```math
b_p\equiv h\pmod p.
\qquad\text{(C20)}
```

This covers $`h`$, possibly together with other survivors, and avoids both 1 and $`D`$. Repeat until no interior survivor remains. At most $`|S|-2`$ primes are used. At every step at most two available primes are forbidden by endpoint protection, so the initial inequality $`\#\{p\in(v,y]\}\gt |S|+2`$ ensures that the choice is possible.

Finally, for every unused prime $`p\le y`$, choose any residue $`b_p`$ avoiding $`1,D\pmod p`$. Such a choice exists for every prime: for $`p=2`$ the two endpoints agree, and for $`p\gt 2`$ at most two of the $`p`$ residue classes are forbidden. These extra choices cannot uncover any already covered point or cover an endpoint. Thus the complete residue family covers exactly $`[1,D]\setminus\{1,D\}`$.

#### 6. Translate to a prime-gap cover and verify admissibility

By the Chinese remainder theorem there is an integer $`N`$ satisfying

```math
N\equiv-b_p\pmod p\qquad(p\le y).
```

Choose $`a\in[1,M]`$ congruent to $`N+1\pmod M`$. Endpoint avoidance gives

```math
a\not\equiv0\pmod p,\qquad a+g\not\equiv0\pmod p
```

for every $`p\le y`$, proving (C1). If $`1\le j\lt g`$, the integer $`h=1+j`$ was covered by some $`b_p`$, and therefore

```math
a+j\equiv1+j-b_p=h-b_p\equiv0\pmod p,
```

proving (C2). If $`n\equiv a\pmod M`$ and $`n\gt y`$, each such divisor $`p\le y`$ is strictly smaller than $`n+j`$, so it is a proper divisor and the intermediate integer is composite.

For a prime $`p\mid M`$, both forms in (C4) are nonzero modulo $`p`$. If $`p\nmid M`$, then $`p\gt y\gt 2`$, and the product $`L_1(t)L_2(t)`$ has at most two roots modulo $`p`$. If $`p\mid g`$, the two roots coincide, which only helps. Hence at least one residue class for $`t`$ makes both forms nonzero. This proves admissibility at every prime, including primes dividing $`g`$.

Finally, $`\log M=\vartheta(y)=(1+o(1))y`$ by the prime number theorem, and $`D\sim g`$. This proves (C3) and completes the covering theorem. $`\square`$

## A uniform interval of gaps between reduced residues

For a prime $`p`$, write $`p\#=\prod_{q\le p}q`$. Let $`\mathcal D(p)`$ be the set of differences between consecutive positive integers coprime to $`p\#`$. This is a periodic sifted set; its members need not be primes.

**Corollary C-RESIDUES.** For every fixed real $`c`$ with $`0\lt c\lt 1/8`$, and every sufficiently large prime $`p`$,

```math
\{g\in2\mathbb N:g\le c p\log_2p/\log_3p\}
\subseteq\mathcal D(p).
\qquad\text{(C23)}
```

The same assertion holds for the internal gaps of the increasing reduced residue system in $`[1,p\#]`$, with no need to include its wraparound gap. If $`N_{\min}(k)`$ denotes the largest even integer such that all positive even integers up to it occur in $`\mathcal D(p_k)`$, then in particular

```math
\liminf_{k\to\infty}
\frac{N_{\min}(k)\log_3p_k}{p_k\log_2p_k}\ge\frac18.
\qquad\text{(C24)}
```

**Proof.** We first record persistence upon adjoining a new prime. Suppose $`Q`$ is an even squarefree integer, $`q\gt 2`$ is a prime not dividing $`Q`$, and $`a,a+g`$ are consecutive integers coprime to $`Q`$. Among the $`q`$ lifts

```math
a+tQ\qquad(0\le t\lt q),
```

at most two have either endpoint divisible by $`q`$. This follows because $`Q`$ is invertible modulo $`q`$, so each of $`a+tQ\equiv0\pmod q`$ and $`a+g+tQ\equiv0\pmod q`$ forbids one class of $`t`$. The two forbidden classes may coincide. Since $`q\gt 2`$, at least one lift preserves both endpoints. Every intervening integer still has its original common prime divisor with $`Q`$, so it is not coprime to $`qQ`$. Thus the gap persists under adjoining $`q`$. If the original gap is internal, with $`1\le a\lt a+g\le Q-1`$, each of its lifts is also internal in $`[1,qQ]`$.

Let $`g_0`$ be an absolute threshold from Theorem C-SUB, enlarged so that

```math
y(g)=8(g+1)\frac{\log_3(g+1)}{\log_2(g+1)}
```

is increasing for $`g\ge g_0`$. Put $`G(p)=c p\log_2p/\log_3p`$. Since $`\log G(p)\sim\log p`$,

```math
y(G(p))=(8c+o(1))p\lt p
```

for all sufficiently large $`p`$. Hence, uniformly for every even $`g`$ with $`g_0\le g\le G(p)`$, the covering modulus in Theorem C-SUB divides $`p\#`$. The theorem gives a gap $`g`$ between integers coprime to that modulus, and persistence while adjoining the remaining primes puts $`g`$ in $`\mathcal D(p)`$.

To deal with the finitely many even $`g\lt g_0`$, an elementary construction suffices. Force the left endpoint to be odd. Assign each even interior offset $`j`$ a distinct prime $`q_j\gt g`$, and impose that the left endpoint be $`-j\pmod{q_j}`$. These compatible congruences preserve both endpoints and cover every interior offset: odd offsets are covered by 2, and even offsets by their assigned primes. Thus each such $`g`$ is a gap among integers coprime to the resulting even squarefree modulus. Taking one threshold larger than all these finitely many assigned primes and adjoining the other primes proves their simultaneous persistence in every sufficiently large $`p\#`$.

For internal gaps, a gap of size $`g\gt 2`$ between integers coprime to any even modulus $`Q`$ cannot cross the boundary of a fundamental period. Indeed, reducing its left endpoint to $`1\le a\le Q-1`$, a crossing would place the consecutive units $`Q-1,Q+1`$ at or inside its endpoints. Absence of an interior unit would then force the entire gap to be $`[Q-1,Q+1]`$, of size 2. For the remaining size 2, the internal gap $`[11,13]`$ modulo 30 persists internally upon adjoining primes greater than 5. This proves (C23), including the internal formulation. Since $`c\lt 1/8`$ is arbitrary and rounding to an even integer is negligible, (C24) follows. $`\square`$

### Comparison for this corollary

Mario Ziller, *On differences between consecutive numbers coprime to primorials*, [arXiv:2007.01808v1](https://arxiv.org/abs/2007.01808v1) (3 July 2020), Proposition 2.7 and Corollary 2.8, proves persistence and the explicit bound $`N_{\min}(k)\ge2k`$. The bound (C24) is asymptotically larger than that identified bound, since $`k\sim p_k/\log p_k`$. This comparison establishes a strict improvement over that particular quantitative baseline; it does not establish priority over all prior work.

Fred B. Holt and Helgi Rudd, *Eratosthenes sieve and the gaps between primes*, [arXiv:1408.6002v1](https://arxiv.org/abs/1408.6002v1) (26 August 2014), Theorem 6.5, already proves that each fixed even gap eventually occurs in the primorial sieve and gives limiting ratios of the corresponding counts. Thus the new content of (C23), relative to that qualitative existence result, is its explicit growing range of gaps at a given sieve stage. The corollary is still a theorem about reduced residues, and makes no assertion that its two endpoints are prime.

## What this repairs, and what remains missing

The construction proves, uniformly in the prescribed even $`g`$, an endpoint-preserving cover with $`M=\exp(o(g))`$. It deals directly with primes dividing the prescribed endpoint difference: they neither create an admissibility obstruction nor force every divisor of $`g`$ to lie below $`y`$.

The forms (C4) are nevertheless a designated admissible pair. Neither the prime number theorem, Brun–Titchmarsh, Bombieri–Vinogradov, a zero-free region, nor a bounded-gap theorem proves that this pair takes prime values simultaneously. For each fixed $`g`$, Dickson's conjecture for these two forms implies infinitely many exact consecutive-prime gaps of size $`g`$, since the cover makes all intervening values composite. This application needs only a two-form instance of Dickson, but it remains an unproved prime-pair assertion.

The construction sharpens the conditional first-occurrence implication. Consider the explicitly stated hypothesis:

**Hypothesis C-PAIR-LINNIK.** There is an absolute constant $`B\gt 1`$ such that, for all sufficiently large even $`g`$, at least one residue $`a`$ supplied by Theorem C-SUB has a prime pair $`n,n+g`$ with

```math
n\equiv a\pmod M,\qquad M\le n\le M^B.
\qquad\text{(C21)}
```

Under this hypothesis, the pair is consecutive and its first left prime $`P_g`$ satisfies

```math
\log P_g\le(8B+o(1))g\frac{\log_3g}{\log_2g}=o(g).
\qquad\text{(C22)}
```

This gives an appropriately small first-occurrence bound for the stronger Erdős rate question once the relation between first occurrences and the missing-gap function is proved, and once every remaining finite gap is separately settled. The hypothesis is **not known**, is not a consequence asserted here of Elliott–Halberstam or GRH, and is not the qualitative two-form Dickson conjecture: it adds substantial uniform quantitative information. It is narrower in the forms it quantifies over than a full prime-tuples assertion, but that does not make its quantitative strength comparable to a qualitative prime-tuples conjecture.

Without a bound such as (C21), a small covering modulus alone says nothing useful about the first prime pair in the covering class.

## Relation to prior covering arguments

Banks–Freiberg–Maynard, arXiv:1404.5094v2 (20 October 2014), Lemma 5.1, supplies a closely related endpoint-preserving cleanup step for an already sparse survivor set. Their Lemma 5.2 creates a tuple at approximately prescribed locations and imposes a small-prime-factor condition on the differences of its selected tuple. Consequently, that lemma cannot simply be quoted for the two exact locations $`1,g+1`$ for arbitrary $`g`$.

The proof above is an elementary variant of the Erdős–Rankin architecture: set most medium-prime residue classes to zero, count smooth or almost-prime-shaped survivors, and spend the remaining large primes to remove them. Its added bookkeeping allows medium primes dividing the protected right endpoint to remain unused, and bounds their contribution by (C9). The other key choice is to avoid zero in the small-prime residue classes, allowing the prime cofactor count (C12)–(C18). No priority claim about this variant, or about its resulting primorial-gap bound, should be made before a dedicated comparison with the literature on gaps between reduced residues.

## Source details and proof dependency map

| Input | Exact use | Scope and assumptions |
|---|---|---|
| Chinese remainder theorem | (C12), construction of $`a`$ | Finite elementary congruence statement |
| Elementary Rankin bound | (C9) | Nonnegative Euler-product upper bound at exponent $`1/2`$ |
| Mertens product theorem | (C15), (C17a) | Ordinary primes; unconditional |
| Montgomery–Vaughan, *The large sieve*, Mathematika 20 (1973), Theorem 2, equation (1.10), pp. 121 and 124–130 | (C13)–(C14) | Uniform Brun–Titchmarsh upper bound, no exceptional-character exclusion |
| Prime number theorem | (C19), (C3) | Counts cleanup primes and estimates the primorial; unconditional |
| Banks–Freiberg–Maynard, arXiv:1404.5094v2, Lemmas 5.1 and 5.2 | Literature comparison only | Not imported as a black-box exact-endpoint construction |
| Hypothesis C-PAIR-LINNIK | (C21)–(C22) only | Explicit unproved simultaneous-primality and uniform first-occurrence input |

Primary source for the Brun–Titchmarsh theorem: H. L. Montgomery and R. C. Vaughan, “The large sieve”, *Mathematika* **20** (1973), 119–134, DOI [10.1112/S0025579300004708](https://doi.org/10.1112/S0025579300004708), [author-hosted PDF](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf). The theorem's printed statement has positive interval origin; the displayed initial-segment version follows by taking that origin to zero from above.

Primary covering comparison: W. D. Banks, T. Freiberg, and J. Maynard, “On limit points of the sequence of normalized prime gaps”, [arXiv:1404.5094v2](https://arxiv.org/abs/1404.5094v2).
