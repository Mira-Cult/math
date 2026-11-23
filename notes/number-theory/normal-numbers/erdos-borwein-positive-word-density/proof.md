# Proof outline: positive density of every fixed binary word

[Return to the theorem (claim 0002)](README.md).

Let $`E=\sum_{m\ge1}(2^m-1)^{-1}`$. Fix a binary word of length $`k`$ and a window of length $`H`$ after position $`N`$, with $`N^a\le H\le N`$ and $`a>7/12`$. An eligible start is one whose full $`k`$-digit block lies in the window.

## Proof outline

Write $`\tau(m)`$ for the number of divisors, $`\omega(m)`$ for the number of distinct prime divisors, and $`e(t)=e^{2\pi i t}`$. Absolute convergence of the Lambert expansion gives

```math
E=\sum_{r\ge1}\tau(r)\,2^{-r},\qquad
e(2^{n-1}E)=\prod_{j\ge0}e\!\left(\tau(n+j)\,2^{-j-1}\right).
```

A $`k`$-word of integer value $`u`$ corresponds to the arc parametrized by $`[u2^{-k},(u+1)2^{-k})`$. Its midpoint has chord distance $`d_k=2\sin(\pi\,2^{-k-1})`$ from its two endpoints.

**Place an exact midpoint term.** Let $`A=2^{2u}`$, choose a sufficiently small fixed $`\theta>0`$, and take odd squarefree $`m`$ with $`b=Am\le N^\theta`$. For each such $`m`$, set $`j_0=\omega(m)+k+1`$. Count an incidence when $`n+j_0=bp`$ with $`p`$ prime and $`n`$ an eligible start. We may impose $`j_0\le C\log\log N`$ for a sufficiently large fixed $`C`$. For large $`N`$, $`p>b`$; multiplicativity gives

```math
\tau(bp)=2^{\omega(m)+1}(2u+1),\qquad
\tau(bp)2^{-j_0-1}=(u+1/2)2^{-k}.
```

No coefficients of $`E`$ are changed. In particular every other divisor term, including any other midpoint incidence, remains in the product.

**Count and isolate genuine incidences.** On the uniform counting measure of eligible starts let $`F(n)`$ be the number of incidences at $`n`$; on the incidence measure, each individual pair of an eligible start and a certifying factorization counts once. For any fixed $`a'\in(7/12,a)`$, the analytic estimates below apply uniformly after shortening the start interval by $`k-1`$ positions:
1. $`\lambda=\mathbb E F\asymp_{a,w}\theta`$ and $`\mathbb E F^2\ll_{a,w}\theta`$, with all parameters fixed before $`N`$. The first estimate uses the uniform short-interval prime count in the interval for $`p`$ and the reciprocal sum over odd squarefree $`m`$. The second counts collisions of certifying factorizations, or uses the one-incidence true valuation envelope at other offsets. At a single offset the prime factor $`p>\sqrt{n+j_0}`$ is unique.
2. For each sufficiently large fixed integer $`W`$, the incidence measure has a central avoidance event $`\mathcal A`$ with probability comparable to its model value $`P_0\ge e^{-4W}`$. If $`R`$ denotes the complete complementary product, omitting only $`j_0`$, its conditional mean chord distance satisfies

```math
\mathbb E_{\mathrm{inc}}\bigl[|R-1|\mid\mathcal A\bigr]
\ll_{a,w}\frac{1+\log^2(W+2)}{W}+o_{N\to\infty;W}(1).
```

The event excludes small terminal-bank deficits, not the actual completed phases. The estimate uses force-weighted comparison on the event itself; subtracting an unconditional tail from a rare-event probability would not suffice. The fixed anchor costs at most $`\Omega(A)`$ extra in the adaptive gcd bound, where $`\Omega`$ counts prime factors with multiplicity. The constant factor $`1/A`$ in the incidence count cancels upon normalizing. Outer sites and the full positive far tail remain in the estimate.

Take $`W`$ so large that the last conditional bound is less than $`d_k/4`$ for all sufficiently large $`N`$. Markov then gives a positive fraction of genuine incidences with $`|R-1|<d_k/2`$. The true phase of each such incidence belongs strictly to the target arc, including for the all-zero and all-one words. If $`F_{\mathrm{good}}`$ counts these incidences, then

```math
\Pr(F_{\mathrm{good}}>0)\ge
\frac{(\mathbb E F_{\mathrm{good}})^2}{\mathbb E F_{\mathrm{good}}^2}
\ \ge\ \frac{(\mathbb E F_{\mathrm{good}})^2}{\mathbb E F^2}
\gg_{a,w}1.
```

There are $`H-k+1\sim H`$ eligible starts. This proves the claim. Shortening uses $`a'`$ because $`H-k+1`$ need not be at least $`N^a`$ at the left endpoint.

## Analytic estimates

- [Fixed-word incidence estimates and anchor transfer](fixed-word-incidences.md).
- [Conditional isolation and the quantitative terminal sieve bank](conditional-isolation.md), especially Sections 1–4 and the source clarification. The central comparison sums finite-order exact-atom errors against the lattice factors and retains the same $`P_0`$ in the weighted estimate. For the unconditional outside of the strip use the adaptive gcd average, not a pointwise bound uniform in the cofactors.
- [Fixed-order force-weighted local comparison](weighted-local-comparison.md) and [size-biased short-interval tail and short Bombieri–Vinogradov input](marked-tail.md). The available interval exponent must be strictly above $`7/12`$, after shrinking it to account for dividing by $`b`$. The normalized log-prime and ordinary-prime measures on each prime interval differ by $`1+O(1/\log(N/b))`$ pointwise, also for nonnegative unbounded force weights.
- [Verification and references](VERIFICATION.md), including the scope of the two independent internal checks.

## Earlier results and acknowledgment

John M. Campbell proved infinitely many occurrences of `11` in [*On the binary digits of the Erdős–Borwein constant*](https://arxiv.org/abs/2605.24160v1). [Captain Sude’s Theorem 1](https://raw.githubusercontent.com/CaptainSude/erdos-borwein-disjunctivity/v1.0.0/paper/erdos-borwein-disjunctivity.tex) gives the prefix lower bound $`N\exp[-C_w(\log\log N)^3]`$ for every fixed word. That lower bound is sublinear. This comparison does not make an exhaustive priority claim.

OpenAI’s GPT-6.2 Astra developed the proof and drafted the original outline under Mira’s guidance. See the [verification notes](VERIFICATION.md) for the scope of the internal checks.
