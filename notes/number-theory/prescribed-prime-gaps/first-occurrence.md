# First occurrences and the two Erdős questions

Mira Cult · 16 November 2026

Let the primes be indexed by $`p_1=2,p_2=3,\ldots`$, and let
$`d_n=p_{n+1}-p_n`$. For a positive even integer $`g`$, define

```math
f(g)=\min\{n\ge1:d_n=g\},\qquad P(g)=p_{f(g)},
```

with both values infinite if there is no occurrence. The notation $`P(g)`$
denotes the first left endpoint; it is different from the pair-counting
function $`P_g(X)`$. For real $`y\ge2`$, let

```math
F(y)=\max_{\substack{2\le g\le y\\g\text{ even}}} f(g).
```

For $`x\ge1`$, let $`r(x)`$ be the smallest positive even integer absent among
$`d_1,\ldots,d_{\lfloor x\rfloor}`$. A finite prefix contains only finitely
many gap values, so this minimum always exists.

## Proposition R1: the exact finite inversion

For every $`x\ge1`$ and $`y\ge2`$,

```math
r(x)\gt y\quad\Longleftrightarrow\quad F(y)\le\lfloor x\rfloor.
```

Indeed, both sides say that every positive even integer at most $`y`$ has an
occurrence by the indicated index. In particular,

```math
r(x)\longrightarrow\infty
\quad\Longleftrightarrow\quad
f(g)\lt \infty\text{ for every positive even }g.
```

For the forward implication, choose $`x`$ with $`r(x)\gt g`$. For the reverse
implication, the maximum of the finitely many indices $`f(g)`$ with $`g\le y`$
is finite; every $`x`$ beyond that maximum has $`r(x)\gt y`$.

This proves the requested equivalence with the one-occurrence question.
It says nothing about the number of occurrences of any individual gap.

## Proposition R2: the stronger rate is exactly a subexponential first-occurrence statement

Assume every positive even gap occurs. The following are equivalent, with
$`g`$ tending to infinity through even integers:

1. $`r(x)/\log x\longrightarrow\infty`$.
2. $`\log F(y)=o(y)`$.
3. $`\log f(g)=o(g)`$.
4. $`\log P(g)=o(g)`$.

**Proof.** Suppose 1 holds. There are $`\lfloor y/2\rfloor`$ different gap
values through $`y`$, so $`F(y)\ge\lfloor y/2\rfloor`$. Put $`x=F(y)-1`$.
At least one gap through $`y`$ is missing at $`x`$, so $`r(x)\le y`$. Since
$`x\to\infty`$, condition 1 gives $`\log(F(y)-1)/y\to0`$; replacing
$`F(y)-1`$ by $`F(y)`$ does not change this limit. Thus 2 holds.

Suppose 2 holds and fix $`A\gt 0`$. For large $`x`$, choose
$`y=2\lceil A\log x/2\rceil`$. Eventually
$`\log F(y)\le y/(2A)\lt \log x`$, so $`F(y)\le\lfloor x\rfloor`$.
Proposition R1 gives $`r(x)\gt y\ge A\log x`$. As $`A`$ was arbitrary, 1 follows.

Condition 2 implies 3 because $`f(g)\le F(g)`$. Conversely, if 3 holds, for
every $`\epsilon\gt 0`$ there is $`g_0`$ such that
$`\log f(g)\le\epsilon g`$ for every even $`g\ge g_0`$. Consequently

```math
\log F(y)\le\max\{\log F(g_0),\epsilon y\},
```

which proves 2.

Finally $`f(g)\le P(g)`$, so 4 implies 3. The classical prime number theorem
in its equivalent nth-prime form $`p_n\sim n\log n`$ gives
$`\log p_n\sim\log n`$. To apply this along the first-occurrence indices, note that for each fixed $`N`$ the
finite list $`d_1,\ldots,d_N`$ has a maximum, and hence $`f(g)\gt N`$ for every
larger $`g`$. Thus $`f(g)\to\infty`$, and
$`\log P(g)\sim\log f(g)`$. Condition 3 implies 4. The prime number theorem
is the only analytic input in this last equivalence. The equivalence of
1--3 is purely elementary. $`\square`$

## What numerical first-occurrence estimates would imply

An effective uniform bound $`f(g)\le B(g)`$ gives

```math
r(x)\gt y\quad\text{whenever}\quad
\max_{\substack{2\le g\le y\\g\text{ even}}} B(g)\le x.
```

A bound $`P(g)\le B(g)`$ also gives $`f(g)\le B(g)`$, and can be refined to
an index bound $`f(g)=\pi(P(g))`$ when a suitable prime-counting estimate is
available. A prime-location bound and an index bound are not the same datum.

For example, a uniform $`f(g)\le\exp(Ag)`$ would give only
$`r(x)\ge(1/A-o(1))\log x`$. A bound
$`f(g)\le\exp(A g\log g)`$ gives a lower bound on the scale
$`\log x/(A\log\log x)`$. Neither bound proves the stronger Erdős limit.
A subexponential bound $`f(g)\le\exp(o(g))`$ does, by Proposition R2.
The existence of some finite first occurrence for each gap, with no uniform
rate, gives no such conclusion.

## Corollary R3: the role of a small covering modulus

Suppose that for each sufficiently large even $`g`$ a complete interior cover
has an even squarefree modulus $`Q_g`$, a reduced pair of endpoint residues
$`a_g,a_g+g`$, and imposed divisors at most $`Y_g`$, with

```math
\log Q_g=o(g),\qquad \log Y_g=o(g).
```

Suppose, in addition, that there is an absolute $`A\gt 0`$ such that these
particular endpoint forms have a prime pair at some

```math
Y_g\lt n\le (Q_g+g+Y_g)^A,\qquad n\equiv a_g\pmod{Q_g}.
```

Then $`n`$ and $`n+g`$ are consecutive by the cover, and
$`\log P(g)=o(g)`$. If the finite exceptional gaps also occur, both Erdős853
questions follow by Propositions R1 and R2.

The additional prime-pair statement is a quantitative two-form analogue
of a Linnik theorem, restricted to the constructed family. It is unproved.
It is not ordinary Linnik's theorem for a single progression and is not
supplied by Elliott--Halberstam, a zero-free region, or qualitative Dickson.
The ordinary pointwise prime-tuples conjecture has no specified uniform
first-occurrence rate, so it is not asserted to imply this quantitative input.
This corollary identifies the exact rate that a successful endpoint theorem
would need; it is not a proof of that theorem.
